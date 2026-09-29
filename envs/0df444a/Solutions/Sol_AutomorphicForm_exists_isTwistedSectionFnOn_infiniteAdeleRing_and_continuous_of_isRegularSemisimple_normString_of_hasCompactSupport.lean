-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/319f3b39-43a3-55f8-9add-2f9078a70ebc

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport

set_option autoImplicit false

open scoped TensorProduct TensorProduct.RightActions

namespace SectionFunctions

section Algebraic

variable {G : Type*} [Group G] (T : Subgroup G)

private theorem isMulRightInvariant_of_forall_commute [MeasurableSpace T] (τ : MeasureTheory.Measure T)
    [τ.IsMulLeftInvariant] (hcomm : ∀ a b : T, a * b = b * a) : τ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : (fun x : T => x * g) = fun x : T => g * x := funext fun x => hcomm x g
  rw [h]
  exact MeasureTheory.map_mul_left_eq_self τ g

private noncomputable def fibreIntegral [MeasurableSpace T] (τ : MeasureTheory.Measure T) (g : G → ℝ) (x : G) : ℝ :=
  ∫ t : T, g ((t : G) * x) ∂τ

private theorem fibreIntegral_nonneg [MeasurableSpace T] (τ : MeasureTheory.Measure T) {g : G → ℝ}
    (hg : ∀ y, 0 ≤ g y) (x : G) : 0 ≤ fibreIntegral T τ g x :=
  MeasureTheory.integral_nonneg fun t => hg ((t : G) * x)

private theorem fibreIntegral_mul_left [MeasurableSpace T] [MeasurableMul T] (τ : MeasureTheory.Measure T)
    [τ.IsMulRightInvariant] (g : G → ℝ) (t₀ : T) (x : G) :
    fibreIntegral T τ g ((t₀ : G) * x) = fibreIntegral T τ g x := by
  show ∫ t : T, g ((t : G) * ((t₀ : G) * x)) ∂τ = ∫ t : T, g ((t : G) * x) ∂τ
  have h : (fun t : T => g ((t : G) * ((t₀ : G) * x))) =
      fun t : T => (fun s : T => g ((s : G) * x)) (t * t₀) := by
    funext t
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [h]
  exact MeasureTheory.integral_mul_right_eq_self (fun s : T => g ((s : G) * x)) t₀

end Algebraic

section Topological

variable {G : Type*} [Group G] [TopologicalSpace G] (T : Subgroup G)

private theorem isCompact_preimage_val (hT : IsClosed (T : Set G)) {K : Set G} (hK : IsCompact K) :
    IsCompact ((fun t : T => (t : G)) ⁻¹' K) :=
  hT.isClosedEmbedding_subtypeVal.isCompact_preimage hK

private theorem continuous_shifted [ContinuousMul G] {g : G → ℝ} (hg : Continuous g) (x : G) :
    Continuous fun t : T => g ((t : G) * x) :=
  hg.comp (continuous_subtype_val.mul continuous_const)

private theorem hasCompactSupport_shifted [ContinuousMul G] [T2Space G] (hT : IsClosed (T : Set G))
    {g : G → ℝ} (hgc : HasCompactSupport g) (x : G) : HasCompactSupport fun t : T => g ((t : G) * x) := by
  refine HasCompactSupport.intro
    (isCompact_preimage_val T hT (IsCompact.image hgc (continuous_id.mul (continuous_const (y := x⁻¹)))))
    fun t ht => ?_
  by_contra h
  exact ht ⟨(t : G) * x, subset_tsupport g h, by simp⟩

open scoped Pointwise in
private theorem continuous_fibreIntegral [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [FirstCountableTopology G] [MeasurableSpace T] [BorelSpace T] (τ : MeasureTheory.Measure T) [τ.IsHaarMeasure]
    (hT : IsClosed (T : Set G)) {g : G → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (fibreIntegral T τ g) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hN, hNx₀⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hS : IsCompact ((fun t : T => (t : G)) ⁻¹' (tsupport g * N⁻¹)) :=
    isCompact_preimage_val T hT (IsCompact.mul hgc hN.inv)
  refine MeasureTheory.continuousAt_of_dominated
    (bound := ((fun t : T => (t : G)) ⁻¹' (tsupport g * N⁻¹)).indicator fun _ => M) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => (continuous_shifted T hg x).aestronglyMeasurable
  · refine Filter.eventually_of_mem hNx₀ fun x hx => MeasureTheory.ae_of_all _ fun t => ?_
    by_cases ht : t ∈ (fun t : T => (t : G)) ⁻¹' (tsupport g * N⁻¹)
    · simpa [ht] using hM ((t : G) * x)
    · have hzero : g ((t : G) * x) = 0 := by
        by_contra hne
        exact ht ⟨(t : G) * x, subset_tsupport g hne, x⁻¹, Set.inv_mem_inv.mpr hx, by simp⟩
      simp [ht, hzero]
  · exact (MeasureTheory.integrableOn_const hS.measure_lt_top.ne).integrable_indicator hS.isClosed.measurableSet
  · exact MeasureTheory.ae_of_all _ fun t => (hg.comp (continuous_const.mul continuous_id)).continuousAt

private theorem fibreIntegral_pos [ContinuousMul G] [T2Space G] [MeasurableSpace T] [BorelSpace T]
    (τ : MeasureTheory.Measure T) [τ.IsHaarMeasure] (hT : IsClosed (T : Set G)) {g : G → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hg0 : ∀ y, 0 ≤ g y) {x : G} (hx : ∃ t : T, 0 < g ((t : G) * x)) :
    0 < fibreIntegral T τ g x := by
  obtain ⟨t, ht⟩ := hx
  refine (MeasureTheory.integral_pos_iff_support_of_nonneg (fun s : T => hg0 ((s : G) * x))
    ((continuous_shifted T hg x).integrable_of_hasCompactSupport (hasCompactSupport_shifted T hT hgc x))).mpr ?_
  exact (continuous_shifted T hg x).isOpen_support.measure_pos τ ⟨t, ht.ne'⟩

open scoped Pointwise in

private theorem exists_invariant_cutoff [IsTopologicalGroup G] [LocallyCompactSpace G] {Ψ : G → G}
    (hΨ : Continuous Ψ) (hinv : ∀ (t : T) (x : G), Ψ ((t : G) * x) = Ψ x)
    (hprop : ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧ Ψ ⁻¹' C ⊆ (T : Set G) * D)
    {C : Set G} (hC : IsCompact C) :
    ∃ ψ : G → ℝ, Continuous ψ ∧ (∀ (t : T) (x : G), ψ ((t : G) * x) = ψ x) ∧
      (∀ x, 0 ≤ ψ x) ∧ (∀ x, Ψ x ∈ C → ψ x = 1) ∧
      ∃ D : Set G, IsCompact D ∧ ∀ x, ψ x ≠ 0 → x ∈ (T : Set G) * D := by
  obtain ⟨f, hfC, -, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
  obtain ⟨D, hD, hDsub⟩ := hprop (tsupport f) hfc
  refine ⟨fun x => f (Ψ x), f.continuous.comp hΨ, fun t x => ?_, fun x => (hf01 (Ψ x)).1,
    fun x hx => hfC hx, D, hD, fun x hx => hDsub (subset_tsupport (⇑f) hx)⟩
  show f (Ψ ((t : G) * x)) = f (Ψ x)
  rw [hinv]

open scoped Pointwise in

private theorem exists_continuous_section [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [FirstCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace T] [BorelSpace T]
    (τ : MeasureTheory.Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant] (hT : IsClosed (T : Set G))
    {Ψ : G → G} (hΨ : Continuous Ψ) (hinv : ∀ (t : T) (x : G), Ψ ((t : G) * x) = Ψ x)
    (hprop : ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧ Ψ ⁻¹' C ⊆ (T : Set G) * D)
    {C : Set G} (hC : IsCompact C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      (∀ x, Ψ x ∈ C → ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧ Continuous w := by
  obtain ⟨ψ, hψ, hψinv, hψ0, hψC, D, hD, hψD⟩ := exists_invariant_cutoff T hΨ hinv hprop hC
  obtain ⟨b, hbD, -, hbc, hb01⟩ :=
    exists_continuous_one_zero_of_isCompact hD isClosed_empty (Set.disjoint_empty D)
  have hb0 : ∀ y, 0 ≤ b y := fun y => (hb01 y).1
  have hβcont : Continuous (fibreIntegral T τ (⇑b)) := continuous_fibreIntegral T τ hT b.continuous hbc
  have hβpos : ∀ x, x ∈ (T : Set G) * D → 0 < fibreIntegral T τ (⇑b) x := by
    rintro x ⟨s, hs, d, hd, rfl⟩
    refine fibreIntegral_pos T τ hT b.continuous hbc hb0 ⟨⟨s, hs⟩⁻¹, ?_⟩
    have hsd : (((⟨s, hs⟩⁻¹ : T) : G)) * (s * d) = d := by simp
    have hbd : b d = 1 := hbD hd
    rw [hsd, hbd]
    exact zero_lt_one
  have hψT : tsupport ψ ⊆ (T : Set G) * D :=
    closure_minimal (fun x hx => hψD x hx) (hT.mul_right_of_isCompact hD)
  have hwcont : Continuous fun x => ψ x * b x / fibreIntegral T τ (⇑b) x := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ (T : Set G) * D
    · exact (hψ.mul b.continuous).continuousAt.div hβcont.continuousAt (hβpos x hx).ne'
    · refine (continuousAt_const (y := (0 : ℝ))).congr (Filter.eventually_of_mem
        ((isClosed_tsupport ψ).isOpen_compl.mem_nhds fun hx' => hx (hψT hx')) fun y hy => ?_)
      simp [image_eq_zero_of_notMem_tsupport hy]
  refine ⟨fun x => ψ x * b x / fibreIntegral T τ (⇑b) x,
    fun x => div_nonneg (mul_nonneg (hψ0 x) (hb0 x)) (fibreIntegral_nonneg T τ hb0 x), hwcont.measurable,
    HasCompactSupport.intro hbc fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy], ?_, hwcont⟩
  intro x hx
  have hx1 : ψ x = 1 := hψC x hx
  have hβx : fibreIntegral T τ (⇑b) x ≠ 0 := (hβpos x (hψD x (by rw [hx1]; exact one_ne_zero))).ne'
  have h : (fun t : T => ψ ((t : G) * x) * b ((t : G) * x) / fibreIntegral T τ (⇑b) ((t : G) * x)) =
      fun t : T => b ((t : G) * x) / fibreIntegral T τ (⇑b) x := by
    funext t
    rw [hψinv t x, hx1, one_mul, fibreIntegral_mul_left T τ (⇑b) t x]
  show ∫ t : T, ψ ((t : G) * x) * b ((t : G) * x) / fibreIntegral T τ (⇑b) ((t : G) * x) ∂τ = 1
  rw [h, MeasureTheory.integral_div]
  exact div_self hβx

end Topological

section PiCarrier

variable {ι : Type*} (R : ι → Type*) [∀ w, CommRing (R w)] [∀ w, TopologicalSpace (R w)]

private def piMatrixContinuousMulEquiv :
    Matrix (Fin 2) (Fin 2) (∀ w, R w) ≃ₜ* ∀ w, Matrix (Fin 2) (Fin 2) (R w) where
  __ := (Matrix.piRingEquiv (n := Fin 2) (β := R)).toMulEquiv
  continuous_toFun :=
    continuous_pi fun w => continuous_matrix fun i j => (continuous_apply w).comp (continuous_id.matrix_elem i j)
  continuous_invFun := continuous_matrix fun i j => continuous_pi fun w => (continuous_apply w).matrix_elem i j

private def piGL : GL (Fin 2) (∀ w, R w) ≃ₜ* ∀ w, GL (Fin 2) (R w) :=
  (Units.mapContinuousMulEquiv (piMatrixContinuousMulEquiv R)).trans ContinuousMulEquiv.piUnits

private theorem piGL_apply_coe (g : GL (Fin 2) (∀ w, R w)) (w : ι) (i j : Fin 2) :
    ((piGL R g w : GL (Fin 2) (R w)) : Matrix (Fin 2) (Fin 2) (R w)) i j =
      (g : Matrix (Fin 2) (Fin 2) (∀ w, R w)) i j w :=
  rfl

private theorem piGL_symm_apply_coe (h : ∀ w, GL (Fin 2) (R w)) (i j : Fin 2) (w : ι) :
    ((piGL R).symm h : Matrix (Fin 2) (Fin 2) (∀ w, R w)) i j w =
      ((h w : GL (Fin 2) (R w)) : Matrix (Fin 2) (Fin 2) (R w)) i j :=
  rfl

end PiCarrier

end SectionFunctions

namespace SectionFunctions

section TwistedStrings

variable {G : Type*} [Monoid G]

private def twistedString (f : G →* G) (δ : G) (k : ℕ) : G :=
  ((List.range k).map fun i => (⇑f)^[i] δ).prod

private theorem twistedString_zero (f : G →* G) (δ : G) : twistedString f δ 0 = 1 := by
  simp [twistedString]

private theorem twistedString_succ (f : G →* G) (δ : G) (k : ℕ) :
    twistedString f δ (k + 1) = twistedString f δ k * (⇑f)^[k] δ := by
  simp [twistedString, List.range_succ]

private theorem map_twistedString {G' : Type*} [Monoid G'] (φ : G →* G') (f : G →* G) (f' : G' →* G')
    (h : ∀ x, φ (f x) = f' (φ x)) (δ : G) (k : ℕ) :
    φ (twistedString f δ k) = twistedString f' (φ δ) k := by
  induction k with
  | zero => simp [twistedString_zero]
  | succ k ih =>
    rw [twistedString_succ, twistedString_succ, map_mul, ih]
    congr 1
    exact (Function.Semiconj.iterate_right (show Function.Semiconj ⇑φ ⇑f ⇑f' from h) k) δ

private theorem twistedString_of_forall_eq {f : G →* G} (hf : ∀ x, f x = x) (δ : G) (k : ℕ) :
    twistedString f δ k = δ ^ k := by
  induction k with
  | zero => simp [twistedString_zero]
  | succ k ih => rw [twistedString_succ, ih, Function.iterate_fixed (hf δ) k, pow_succ]

private theorem iterate_two_mul_of_forall_eq {f : G →* G} (hf : ∀ x, f (f x) = x) (δ : G) (m : ℕ) :
    (⇑f)^[2 * m] δ = δ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : (⇑f)^[2] δ = δ := hf δ
    rw [mul_add, mul_one, Function.iterate_add_apply, h2, ih]

private theorem twistedString_two_mul {f : G →* G} (hf : ∀ x, f (f x) = x) (δ : G) (m : ℕ) :
    twistedString f δ (2 * m) = (δ * f δ) ^ m := by
  induction m with
  | zero => simp [twistedString_zero]
  | succ m ih =>
    have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [h, twistedString_succ, twistedString_succ, ih, Function.iterate_succ_apply',
      iterate_two_mul_of_forall_eq hf δ m, pow_succ, mul_assoc]

end TwistedStrings

section RegularTransport

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem coe_glMap (e : R →+* S) (g : GL (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.map e g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      (g : Matrix (Fin 2) (Fin 2) R).map e :=
  Matrix.ext fun i j => by simp [Matrix.GeneralLinearGroup.map_apply]

private theorem isRegularSemisimple_glMap (e : R →+* S) {g : GL (Fin 2) R}
    (hg : AutomorphicForm.IsRegularSemisimple g) :
    AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.map e g) := by
  unfold AutomorphicForm.IsRegularSemisimple at hg ⊢
  rw [coe_glMap]
  set M : Matrix (Fin 2) (Fin 2) R := (g : Matrix (Fin 2) (Fin 2) R) with hM
  have htr : Matrix.trace (M.map e) = e (Matrix.trace M) := by
    simp [Matrix.trace]
  have hdet : Matrix.det (M.map e) = e (Matrix.det M) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hdisc : Matrix.trace (M.map e) ^ 2 - 4 * Matrix.det (M.map e) =
      e (Matrix.trace M ^ 2 - 4 * Matrix.det M) := by
    rw [htr, hdet]
    simp [map_ofNat]
  rw [hdisc]
  exact hg.map e

private theorem glMap_eq_self_of_forall_eq {τ : R →+* R} (hτ : ∀ a, τ a = a) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map τ g = g :=
  Units.ext (Matrix.ext fun i j => by simp [Matrix.GeneralLinearGroup.map_apply, hτ])

private theorem glMap_glMap_eq_self_of_forall_eq {τ : R →+* R} (hτ : ∀ a, τ (τ a) = a) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map τ (Matrix.GeneralLinearGroup.map τ g) = g :=
  Units.ext (Matrix.ext fun i j => by simp [Matrix.GeneralLinearGroup.map_apply, hτ])

end RegularTransport

section GLTransport

variable {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]

private def matrixContinuousMulEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    Matrix (Fin 2) (Fin 2) A ≃ₜ* Matrix (Fin 2) (Fin 2) B where
  __ := (e.mapMatrix (m := Fin 2)).toMulEquiv
  continuous_toFun := continuous_id.matrix_map he
  continuous_invFun := continuous_id.matrix_map he'

private def glContinuousMulEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    GL (Fin 2) A ≃ₜ* GL (Fin 2) B :=
  Units.mapContinuousMulEquiv (matrixContinuousMulEquiv e he he')

private theorem glContinuousMulEquiv_apply (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (g : GL (Fin 2) A) : glContinuousMulEquiv e he he' g = Matrix.GeneralLinearGroup.map e.toRingHom g :=
  Units.ext (Matrix.ext fun _ _ => rfl)

private theorem glContinuousMulEquiv_symm_apply (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (h : GL (Fin 2) B) :
    (glContinuousMulEquiv e he he').symm h = Matrix.GeneralLinearGroup.map e.symm.toRingHom h :=
  Units.ext (Matrix.ext fun _ _ => rfl)

private theorem glContinuousMulEquiv_trans {C : Type*} [CommRing C] [TopologicalSpace C] (e₁ : A ≃+* B)
    (h₁ : Continuous e₁) (h₁' : Continuous e₁.symm) (e₂ : B ≃+* C) (h₂ : Continuous e₂) (h₂' : Continuous e₂.symm) :
    (glContinuousMulEquiv e₁ h₁ h₁').trans (glContinuousMulEquiv e₂ h₂ h₂') =
      glContinuousMulEquiv (e₁.trans e₂) (h₂.comp h₁) (h₁'.comp h₂') :=
  ContinuousMulEquiv.ext fun _ => Units.ext (Matrix.ext fun _ _ => rfl)

end GLTransport

end SectionFunctions

namespace TwistedOrbitProperness

open AutomorphicForm

section Countability

open TopologicalSpace NumberField

section GLCarrier

variable (A : Type) [CommRing A] [TopologicalSpace A]

private theorem secondCountableTopology_gl [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

end GLCarrier

section Tensor

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

private theorem secondCountableTopology_tensor [SecondCountableTopology A] : SecondCountableTopology (L ⊗[K] A) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A (L ⊗[K] A)
  have hq : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  exact hq.isQuotientMap.secondCountableTopology hq.isOpenMap

end Tensor

section Arch

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ w : InfinitePlace K, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))

end Arch

end Countability

section ArchTransport

open NumberField TopologicalSpace

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private noncomputable def archIdentEquiv : (L ⊗[K] InfiniteAdeleRing K) ≃+* InfiniteAdeleRing L :=
  (Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)).toRingEquiv.trans
    (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv

private theorem coe_archIdentEquiv : ⇑(archIdentEquiv K L) = ⇑(archIdent K L) := rfl

private theorem archIdent_comp_algebraMap :
    (archIdent K L).comp (algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)) =
      (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).conorm :=
  RingHom.ext fun _ => rfl

private theorem coe_archIdentGL (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    ((archIdentGL K L g : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))
      = (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).map (archIdent K L) := by
  ext i j
  simp [archIdentGL, Matrix.GeneralLinearGroup.map_apply]

private noncomputable def archIdentGLInv :
    GL (Fin 2) (InfiniteAdeleRing L) →* GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (archIdentEquiv K L).symm.toRingHom

private theorem coe_archIdentGLInv (h : GL (Fin 2) (InfiniteAdeleRing L)) :
    ((archIdentGLInv K L h : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      = (h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)).map (archIdentEquiv K L).symm := by
  ext i j
  simp [archIdentGLInv, Matrix.GeneralLinearGroup.map_apply]

private theorem archIdentGLInv_archIdentGL (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    archIdentGLInv K L (archIdentGL K L g) = g := by
  apply Units.ext
  ext i j
  rw [coe_archIdentGLInv, Matrix.map_apply, coe_archIdentGL, Matrix.map_apply, ← coe_archIdentEquiv]
  exact (archIdentEquiv K L).symm_apply_apply _

private theorem archIdentGL_archIdentGLInv (h : GL (Fin 2) (InfiniteAdeleRing L)) :
    archIdentGL K L (archIdentGLInv K L h) = h := by
  apply Units.ext
  ext i j
  rw [coe_archIdentGL, Matrix.map_apply, coe_archIdentGLInv, Matrix.map_apply, ← coe_archIdentEquiv]
  exact (archIdentEquiv K L).apply_symm_apply _

variable [FiniteDimensional K L]

private theorem continuous_archIdent : Continuous (archIdent K L) := by
  haveI := isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  refine IsModuleTopology.continuous_of_ringHom (R := InfiniteAdeleRing K) (archIdent K L) ?_
  rw [archIdent_comp_algebraMap]
  exact M4aHerbrand.ArchSemilocal.continuous_conorm (K := K) (L := L)

private theorem isOpenMap_archIdent : IsOpenMap (archIdent K L) := by
  haveI := isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := locallyCompactSpace_tensor K L (InfiniteAdeleRing K)
  haveI := secondCountableTopology_infiniteAdeleRing K
  haveI := secondCountableTopology_tensor K L (InfiniteAdeleRing K)
  exact (archIdent K L).toAddMonoidHom.isOpenMap_of_sigmaCompact (archIdentEquiv K L).surjective
    (continuous_archIdent K L)

private noncomputable def archIdentHomeomorph : (L ⊗[K] InfiniteAdeleRing K) ≃ₜ InfiniteAdeleRing L :=
  (archIdentEquiv K L).toEquiv.toHomeomorphOfContinuousOpen (continuous_archIdent K L) (isOpenMap_archIdent K L)

private theorem continuous_archIdentEquiv_symm : Continuous (archIdentEquiv K L).symm :=
  (archIdentHomeomorph K L).symm.continuous

private theorem continuous_archIdentGL : Continuous (archIdentGL K L) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : (Units.val ∘ archIdentGL K L) = fun g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
        (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).map (archIdent K L) :=
      funext fun g => coe_archIdentGL K L g
    rw [h]
    exact Units.continuous_val.matrix_map (continuous_archIdent K L)
  · have h : (fun g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          ((archIdentGL K L g)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)).val) =
        fun g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          ((g⁻¹ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).map (archIdent K L) :=
      funext fun g => by rw [← map_inv, coe_archIdentGL]
    rw [h]
    exact Units.continuous_coe_inv.matrix_map (continuous_archIdent K L)

private theorem continuous_archIdentGLInv : Continuous (archIdentGLInv K L) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : (Units.val ∘ archIdentGLInv K L) = fun g : GL (Fin 2) (InfiniteAdeleRing L) =>
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)).map (archIdentEquiv K L).symm :=
      funext fun g => coe_archIdentGLInv K L g
    rw [h]
    exact Units.continuous_val.matrix_map (continuous_archIdentEquiv_symm K L)
  · have h : (fun g : GL (Fin 2) (InfiniteAdeleRing L) =>
          ((archIdentGLInv K L g)⁻¹ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).val) =
        fun g : GL (Fin 2) (InfiniteAdeleRing L) =>
          ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)).map
            (archIdentEquiv K L).symm :=
      funext fun g => by rw [← map_inv, coe_archIdentGLInv]
    rw [h]
    exact Units.continuous_coe_inv.matrix_map (continuous_archIdentEquiv_symm K L)

private noncomputable def archIdentGLHomeomorph :
    GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ GL (Fin 2) (InfiniteAdeleRing L) where
  toFun := archIdentGL K L
  invFun := archIdentGLInv K L
  left_inv := archIdentGLInv_archIdentGL K L
  right_inv := archIdentGL_archIdentGLInv K L
  continuous_toFun := continuous_archIdentGL K L
  continuous_invFun := continuous_archIdentGLInv K L

private theorem coe_archIdentGLHomeomorph : ⇑(archIdentGLHomeomorph K L) = ⇑(archIdentGL K L) := rfl

private noncomputable def archIdentGLEquiv :
    GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* GL (Fin 2) (InfiniteAdeleRing L) :=
  { archIdentGLHomeomorph K L with map_mul' := (archIdentGL K L).map_mul }

private theorem coe_archIdentGLEquiv : ⇑(archIdentGLEquiv K L) = ⇑(archIdentGL K L) := rfl

private noncomputable def archFactors :
    GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* ∀ w : InfinitePlace L, GL (Fin 2) w.Completion :=
  (archIdentGLEquiv K L).trans (SectionFunctions.piGL fun w : InfinitePlace L => w.Completion)

private theorem archFactors_apply_coe (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (w : InfinitePlace L)
    (i j : Fin 2) :
    ((archFactors K L g w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j =
      archIdent K L ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i j) w := by
  show ((SectionFunctions.piGL (fun w : InfinitePlace L => w.Completion) (archIdentGL K L g) w :
      GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
  rw [SectionFunctions.piGL_apply_coe, coe_archIdentGL, Matrix.map_apply]

end ArchTransport

section Generic

variable {G : Type*} [Group G]

private theorem mul_prod_range_iterate (f : G →* G) {t δ : G} (h : t * δ = δ * f t) (n : ℕ) :
    t * ((List.range n).map fun i => (⇑f)^[i] δ).prod =
      ((List.range n).map fun i => (⇑f)^[i] δ).prod * (⇑f)^[n] t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, ← mul_assoc, ih, mul_assoc, mul_assoc, Function.iterate_succ_apply]
    congr 1
    have h' := congrArg ((⇑f)^[n]) h
    rwa [iterate_map_mul, iterate_map_mul] at h'

end Generic

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

private theorem twistedCentralizer_le_centralizer_normString_of_iterate (σ : L ≃ₐ[K] L)
    (hσ : ∀ t : GL (Fin 2) (L ⊗[K] A), (⇑(sigmaGL K L A σ))^[Module.finrank K L] t = t)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  have ht' : t * δ * (sigmaGL K L A σ t)⁻¹ = δ := ht
  have key := mul_prod_range_iterate (sigmaGL K L A σ) (mul_inv_eq_iff_eq_mul.mp ht')
    (Module.finrank K L)
  rw [hσ t] at key
  exact key

private theorem sigmaTensor_mul_apply (σ σ' : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    sigmaTensor K L A (σ * σ') z = sigmaTensor K L A σ (sigmaTensor K L A σ' z) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.mul_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem sigmaTensor_one_apply (z : L ⊗[K] A) : sigmaTensor K L A 1 z = z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.one_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem sigmaGL_mul_apply (σ σ' : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] A)) :
    sigmaGL K L A (σ * σ') g = sigmaGL K L A σ (sigmaGL K L A σ' g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A (σ * σ')) g i j =
    Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ)
      (Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ') g) i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_mul_apply]

private theorem sigmaGL_one_apply (g : GL (Fin 2) (L ⊗[K] A)) : sigmaGL K L A 1 g = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A 1) g i j = g i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_one_apply]

private theorem sigmaGL_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] g = sigmaGL K L A (σ ^ n) g := by
  induction n with
  | zero => simp [sigmaGL_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaGL_mul_apply]

private theorem pow_finrank_eq_one [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _
    (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

private theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (g : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] g = g := by
  rw [sigmaGL_iterate, pow_finrank_eq_one, sigmaGL_one_apply]

private theorem twistedCentralizer_le_centralizer_normString [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) :=
  twistedCentralizer_le_centralizer_normString_of_iterate K L A σ
    (sigmaGL_iterate_finrank K L A σ) δ

private theorem sigmaTensor_tmul (σ : L ≃ₐ[K] L) (x : L) (a : A) :
    sigmaTensor K L A σ (x ⊗ₜ a) = σ x ⊗ₜ a := by
  simp [sigmaTensor]

end Twisted

end TwistedOrbitProperness

set_option autoImplicit false

namespace SigmaCycleDescent

open scoped Pointwise in

private def IsTwistedProper {G : Type*} [Group G] [TopologicalSpace G] (θ : G →* G) (δ : G) : Prop :=
  ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
    (fun x => x⁻¹ * δ * θ x) ⁻¹' C ⊆ (AutomorphicForm.sigmaCentralizer θ δ : Set G) * D

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G]

private theorem isTwistedProper_iff (θ : G →* G) (δ : G) :
    IsTwistedProper θ δ ↔ ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
      ∀ x : G, x⁻¹ * δ * θ x ∈ C →
        ∃ t ∈ AutomorphicForm.sigmaCentralizer θ δ, ∃ d ∈ D, t * d = x := by
  unfold IsTwistedProper
  refine forall₂_congr fun C _ => exists_congr fun D => and_congr_right fun _ => ?_
  constructor
  · intro h x hx
    simpa only [Set.mem_mul, SetLike.mem_coe] using h hx
  · intro h x hx
    simpa only [Set.mem_mul, SetLike.mem_coe] using h x hx

private theorem isTwistedProper_of_continuousMulEquiv {G' : Type*} [Group G'] [TopologicalSpace G']
    (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G') (hθ : ∀ x, e (θ x) = θ' (e x)) (δ : G)
    (h : IsTwistedProper θ δ) : IsTwistedProper θ' (e δ) := by
  rw [isTwistedProper_iff] at h ⊢
  intro C hC
  obtain ⟨D, hD, hfac⟩ := h (e ⁻¹' C) (e.toHomeomorph.isCompact_preimage.2 hC)
  refine ⟨e '' D, hD.image e.continuous, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : x⁻¹ * δ * θ x ∈ e ⁻¹' C := by
    show e (x⁻¹ * δ * θ x) ∈ C
    rwa [map_mul, map_mul, map_inv, hθ]
  obtain ⟨t, ht, d, hd, rfl⟩ := hfac x hx
  refine ⟨e t, ?_, e d, ⟨d, hd, rfl⟩, (map_mul e t d).symm⟩
  rw [AutomorphicForm.mem_sigmaCentralizer_iff] at ht ⊢
  rw [← hθ, ← map_inv, ← map_mul, ← map_mul, ht]

end Generic

section Product

variable {ι : Type*} {H : ι → Type*} [∀ i, Group (H i)]

private def piTwist (θ : ∀ i, H i →* H i) : (∀ i, H i) →* ∀ i, H i :=
  MonoidHom.pi fun i => (θ i).comp (Pi.evalMonoidHom H i)

private theorem piTwist_apply (θ : ∀ i, H i →* H i) (x : ∀ i, H i) (i : ι) : piTwist θ x i = θ i (x i) :=
  rfl

variable [∀ i, TopologicalSpace (H i)]

private theorem isTwistedProper_piTwist (θ : ∀ i, H i →* H i) (δ : ∀ i, H i)
    (h : ∀ i, IsTwistedProper (θ i) (δ i)) : IsTwistedProper (piTwist θ) δ := by
  simp only [isTwistedProper_iff] at h ⊢
  intro C hC
  choose D hD hfac using fun i => h i ((fun x : ∀ j, H j => x i) '' C) (hC.image (continuous_apply i))
  refine ⟨Set.pi Set.univ D, isCompact_univ_pi hD, fun x hx => ?_⟩
  have hxi : ∀ i, (x i)⁻¹ * δ i * θ i (x i) ∈ (fun y : ∀ j, H j => y i) '' C := fun i =>
    ⟨x⁻¹ * δ * piTwist θ x, hx, rfl⟩
  choose t ht d hd htd using fun i => hfac i (x i) (hxi i)
  refine ⟨t, ?_, d, fun i _ => hd i, funext htd⟩
  rw [AutomorphicForm.mem_sigmaCentralizer_iff]
  funext i
  simpa only [Pi.mul_apply, Pi.inv_apply, piTwist_apply] using
    (AutomorphicForm.mem_sigmaCentralizer_iff.1 (ht i))

end Product

section Regularity

variable {F : Type*} [Field F] [CharZero F]

private theorem isRegularSemisimple_of_pow {g : GL (Fin 2) F} {k : ℕ}
    (hk : AutomorphicForm.IsRegularSemisimple (g ^ k)) : AutomorphicForm.IsRegularSemisimple g := by
  rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero] at hk ⊢
  intro hdisc
  apply hk
  set M : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hM
  set lam : F := Matrix.trace M / 2 with hlam
  have htr : Matrix.trace M = 2 * lam := by rw [hlam]; ring
  have hdet : Matrix.det M = lam ^ 2 := by
    have : Matrix.trace M ^ 2 = 4 * Matrix.det M := sub_eq_zero.1 hdisc
    rw [htr] at this
    linear_combination (-1 / 4 : F) * this
  set N : Matrix (Fin 2) (Fin 2) F := M - Matrix.scalar (Fin 2) lam with hN
  have hNtr : Matrix.trace N = 0 := by
    rw [hN, Matrix.trace_sub, htr, Matrix.trace_fin_two]
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    ring
  have hNsq : N * N = 0 := by
    have h00 : N 0 0 + N 1 1 = 0 := by simpa only [Matrix.trace_fin_two] using hNtr
    have hdetN : N 0 0 * N 1 1 - N 0 1 * N 1 0 = 0 := by
      have hd := hdet
      rw [Matrix.det_fin_two] at hd
      have htr' : M 0 0 + M 1 1 = 2 * lam := by simpa only [Matrix.trace_fin_two] using htr
      have e00 : N 0 0 = M 0 0 - lam := by simp [hN]
      have e11 : N 1 1 = M 1 1 - lam := by simp [hN]
      have e01 : N 0 1 = M 0 1 := by simp [hN]
      have e10 : N 1 0 = M 1 0 := by simp [hN]
      rw [e00, e11, e01, e10]
      linear_combination hd - lam * htr'
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, Fin.zero_eta, Fin.mk_one,
        Fin.isValue]
    · linear_combination N 0 0 * h00 - hdetN
    · linear_combination N 0 1 * h00
    · linear_combination N 1 0 * h00
    · linear_combination N 1 1 * h00 - hdetN
  have hMN : M = lam • (1 : Matrix (Fin 2) (Fin 2) F) + N := by
    rw [hN]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
  have hpow : ∀ n : ℕ, ∃ c : F, M ^ n = (lam ^ n) • (1 : Matrix (Fin 2) (Fin 2) F) + c • N := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨lam ^ n + c * lam, ?_⟩
      rw [pow_succ, hc, hMN]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hNsq, smul_zero,
        add_zero, smul_add, smul_smul, add_smul, pow_succ, mul_comm]
      abel
  obtain ⟨c, hc⟩ := hpow k
  have hval : ((g ^ k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = M ^ k := by
    rw [hM, Units.val_pow_eq_pow_val]
  have htrk : Matrix.trace (M ^ k) = 2 * lam ^ k := by
    rw [hc, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, hNtr, smul_zero,
      add_zero, smul_eq_mul, Fintype.card_fin]
    push_cast
    ring
  have hdetk : Matrix.det (M ^ k) = lam ^ (2 * k) := by
    rw [Matrix.det_pow, hdet, ← pow_mul]
  rw [hval, htrk, hdetk]
  ring

end Regularity

section Cycle

variable {H : Type*} [Group H]

private def cycleTwist (α : H →* H) (m : ℕ) : (Fin (m + 1) → H) →* (Fin (m + 1) → H) where
  toFun x := (Fin.snoc (fun j : Fin m => x j.succ) (α (x 0)) : Fin (m + 1) → H)
  map_one' := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc]
  map_mul' x y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc]

private theorem cycleTwist_castSucc (α : H →* H) {m : ℕ} (x : Fin (m + 1) → H) (j : Fin m) :
    cycleTwist α m x j.castSucc = x j.succ := by
  simp [cycleTwist, Fin.snoc_castSucc]

private theorem cycleTwist_last (α : H →* H) {m : ℕ} (x : Fin (m + 1) → H) :
    cycleTwist α m x (Fin.last m) = α (x 0) := by
  simp [cycleTwist, Fin.snoc_last]

private def cycleNorm {m : ℕ} (δ : Fin (m + 1) → H) : H :=
  Fin.partialProd (Fin.init δ) (Fin.last m) * δ (Fin.last m)

private theorem partialProd_init_succ {m : ℕ} (δ : Fin (m + 1) → H) (j : Fin m) :
    Fin.partialProd (Fin.init δ) j.succ = Fin.partialProd (Fin.init δ) j.castSucc * δ j.castSucc := by
  rw [Fin.partialProd_succ]
  rfl

variable [TopologicalSpace H] [IsTopologicalGroup H]

private theorem continuous_partialProd_init {m : ℕ} (i : Fin (m + 1)) :
    Continuous fun c : Fin (m + 1) → H => Fin.partialProd (Fin.init c) i := by
  induction i using Fin.induction with
  | zero => simp only [Fin.partialProd_zero]; exact continuous_const
  | succ j ih =>
    simp_rw [partialProd_init_succ]
    exact ih.mul (continuous_apply _)

private theorem isTwistedProper_cycleTwist (α : H →* H) {m : ℕ} (δ : Fin (m + 1) → H)
    (h : IsTwistedProper α (cycleNorm δ)) : IsTwistedProper (cycleTwist α m) δ := by
  rw [isTwistedProper_iff] at h ⊢
  intro C hC

  set P : Fin (m + 1) → H := Fin.partialProd (Fin.init δ) with hP
  let Q : (Fin (m + 1) → H) → Fin (m + 1) → H := fun c => Fin.partialProd (Fin.init c)
  have hQcont : Continuous fun c : Fin (m + 1) → H => Q c (Fin.last m) * c (Fin.last m) :=
    (continuous_partialProd_init (Fin.last m)).mul (continuous_apply _)
  obtain ⟨D₀, hD₀, hfac⟩ := h _ (hC.image hQcont)
  let build : H × (Fin (m + 1) → H) → Fin (m + 1) → H := fun p i => (P i)⁻¹ * p.1 * Q p.2 i
  have hbuild : Continuous build :=
    continuous_pi fun i => (continuous_const.mul continuous_fst).mul
      ((continuous_partialProd_init i).comp continuous_snd)
  refine ⟨build '' (D₀ ×ˢ C), (hD₀.prod hC).image hbuild, fun x hx => ?_⟩
  set c : Fin (m + 1) → H := x⁻¹ * δ * cycleTwist α m x with hc

  have hcoord : ∀ i : Fin (m + 1), x i = (P i)⁻¹ * x 0 * Q c i := by
    intro i
    induction i using Fin.induction with
    | zero =>
      have hP0 : P 0 = 1 := Fin.partialProd_zero _
      have hQ0 : Q c 0 = 1 := Fin.partialProd_zero _
      rw [hP0, hQ0, inv_one, one_mul, mul_one]
    | succ j ih =>
      have hcj : c j.castSucc = (x j.castSucc)⁻¹ * δ j.castSucc * x j.succ := by
        simp only [hc, Pi.mul_apply, Pi.inv_apply, cycleTwist_castSucc]
      have hxsucc : x j.succ = (δ j.castSucc)⁻¹ * x j.castSucc * c j.castSucc := by
        rw [hcj]; group
      have hPs : P j.succ = P j.castSucc * δ j.castSucc := partialProd_init_succ δ j
      have hQs : Q c j.succ = Q c j.castSucc * c j.castSucc := partialProd_init_succ c j
      rw [hxsucc, ih, hPs, hQs]
      group

  have hclose : (x 0)⁻¹ * cycleNorm δ * α (x 0) = Q c (Fin.last m) * c (Fin.last m) := by
    have hlast : c (Fin.last m) = (x (Fin.last m))⁻¹ * δ (Fin.last m) * α (x 0) := by
      simp only [hc, Pi.mul_apply, Pi.inv_apply, cycleTwist_last]
    rw [hlast, hcoord (Fin.last m)]
    show (x 0)⁻¹ * (P (Fin.last m) * δ (Fin.last m)) * α (x 0) = _
    group
  obtain ⟨t, ht, d, hd, htd⟩ := hfac (x 0) (by rw [hclose]; exact ⟨c, hx, rfl⟩)
  rw [AutomorphicForm.mem_sigmaCentralizer_iff] at ht
  refine ⟨fun i => (P i)⁻¹ * t * P i, ?_, build (d, c), ⟨(d, c), ⟨hd, hx⟩, rfl⟩, ?_⟩
  ·
    rw [AutomorphicForm.mem_sigmaCentralizer_iff]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Pi.mul_apply, Pi.inv_apply, cycleTwist_last]
      have hP0 : P 0 = 1 := Fin.partialProd_zero _
      have ht' : t * (P (Fin.last m) * δ (Fin.last m)) * (α t)⁻¹ = P (Fin.last m) * δ (Fin.last m) := ht
      rw [hP0, inv_one, one_mul, mul_one]
      calc (P (Fin.last m))⁻¹ * t * P (Fin.last m) * δ (Fin.last m) * (α t)⁻¹
          = (P (Fin.last m))⁻¹ * (t * (P (Fin.last m) * δ (Fin.last m)) * (α t)⁻¹) := by group
        _ = (P (Fin.last m))⁻¹ * (P (Fin.last m) * δ (Fin.last m)) := by rw [ht']
        _ = δ (Fin.last m) := by group
    · simp only [Pi.mul_apply, Pi.inv_apply, cycleTwist_castSucc]
      have hPs : P j.succ = P j.castSucc * δ j.castSucc := partialProd_init_succ δ j
      rw [hPs]
      group
  ·
    funext i
    simp only [Pi.mul_apply, build]
    rw [hcoord i, ← htd]
    group

end Cycle

section Normalisation

variable {H : Type*} [Group H] [TopologicalSpace H]

private def stepTwist {m : ℕ} (α : Fin (m + 1) → (H ≃ₜ* H)) : (Fin (m + 1) → H) →* (Fin (m + 1) → H) where
  toFun x := (Fin.snoc (fun j : Fin m => α j.castSucc (x j.succ)) (α (Fin.last m) (x 0)) : Fin (m + 1) → H)
  map_one' := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc]
  map_mul' x y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc]

private theorem stepTwist_castSucc {m : ℕ} (α : Fin (m + 1) → (H ≃ₜ* H)) (x : Fin (m + 1) → H) (j : Fin m) :
    stepTwist α x j.castSucc = α j.castSucc (x j.succ) := by
  simp [stepTwist, Fin.snoc_castSucc]

private theorem stepTwist_last {m : ℕ} (α : Fin (m + 1) → (H ≃ₜ* H)) (x : Fin (m + 1) → H) :
    stepTwist α x (Fin.last m) = α (Fin.last m) (x 0) := by
  simp [stepTwist, Fin.snoc_last]

private def accum {m : ℕ} (α : Fin (m + 1) → (H ≃ₜ* H)) (i : Fin (m + 1)) : H ≃ₜ* H :=
  Fin.induction (motive := fun _ => H ≃ₜ* H) (ContinuousMulEquiv.refl H)
    (fun j βj => (α j.castSucc).trans βj) i

private theorem accum_zero {m : ℕ} (α : Fin (m + 1) → (H ≃ₜ* H)) :
    accum α 0 = ContinuousMulEquiv.refl H :=
  Fin.induction_zero _ _

private theorem accum_succ {m : ℕ} (α : Fin (m + 1) → (H ≃ₜ* H)) (j : Fin m) :
    accum α j.succ = (α j.castSucc).trans (accum α j.castSucc) :=
  Fin.induction_succ _ _ _

private def accumEquiv {m : ℕ} (α : Fin (m + 1) → (H ≃ₜ* H)) : (Fin (m + 1) → H) ≃ₜ* (Fin (m + 1) → H) where
  toFun x i := accum α i (x i)
  invFun y i := (accum α i).symm (y i)
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp
  map_mul' x y := by funext i; simp
  continuous_toFun := continuous_pi fun i => (accum α i).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (accum α i).symm.continuous.comp (continuous_apply i)

private theorem accumEquiv_apply {m : ℕ} (α : Fin (m + 1) → (H ≃ₜ* H)) (x : Fin (m + 1) → H) (i : Fin (m + 1)) :
    accumEquiv α x i = accum α i (x i) :=
  rfl

private def closing {m : ℕ} (α : Fin (m + 1) → (H ≃ₜ* H)) : H ≃ₜ* H :=
  (α (Fin.last m)).trans (accum α (Fin.last m))

private theorem accumEquiv_stepTwist {m : ℕ} (α : Fin (m + 1) → (H ≃ₜ* H)) (x : Fin (m + 1) → H) :
    accumEquiv α (stepTwist α x) = cycleTwist (closing α).toMonoidHom m (accumEquiv α x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [accumEquiv_apply, stepTwist_last, cycleTwist_last, accumEquiv_apply, accum_zero]
    rfl
  · rw [accumEquiv_apply, stepTwist_castSucc, cycleTwist_castSucc, accumEquiv_apply, accum_succ]
    rfl

variable [IsTopologicalGroup H]

private theorem isTwistedProper_stepTwist {m : ℕ} (α : Fin (m + 1) → (H ≃ₜ* H)) (δ : Fin (m + 1) → H)
    (h : IsTwistedProper (closing α).toMonoidHom (cycleNorm (accumEquiv α δ))) :
    IsTwistedProper (stepTwist α) δ := by
  have h1 : IsTwistedProper (cycleTwist (closing α).toMonoidHom m) (accumEquiv α δ) :=
    isTwistedProper_cycleTwist _ _ h
  have h2 := isTwistedProper_of_continuousMulEquiv (accumEquiv α).symm _ (stepTwist α)
    (fun y => by
      apply (accumEquiv α).injective
      rw [accumEquiv_stepTwist, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply])
    _ h1
  simpa using h2

end Normalisation

section Orbits

variable {ι : Type*} {H : Type*} [Group H] [TopologicalSpace H]

private def permTwist (π : Equiv.Perm ι) (a : ι → (H ≃ₜ* H)) : (ι → H) →* (ι → H) where
  toFun y w := a w (y (π w))
  map_one' := by funext w; simp
  map_mul' y z := by funext w; simp

private theorem permTwist_apply (π : Equiv.Perm ι) (a : ι → (H ≃ₜ* H)) (y : ι → H) (w : ι) :
    permTwist π a y w = a w (y (π w)) :=
  rfl

private def orbitSetoid (π : Equiv.Perm ι) : Setoid ι :=
  ⟨π.SameCycle, ⟨Equiv.Perm.SameCycle.refl π, fun h => h.symm, fun h h' => h.trans h'⟩⟩

private noncomputable def orbitLen (π : Equiv.Perm ι) (o : Quotient (orbitSetoid π)) : ℕ :=
  Function.minimalPeriod (⇑π) o.out - 1

private noncomputable def orbitPt (π : Equiv.Perm ι) (o : Quotient (orbitSetoid π)) (k : Fin (orbitLen π o + 1)) :
    ι :=
  (⇑π)^[k] o.out

private theorem orbitPt_succ (π : Equiv.Perm ι) (o : Quotient (orbitSetoid π)) (j : Fin (orbitLen π o)) :
    orbitPt π o j.succ = π (orbitPt π o j.castSucc) := by
  simp only [orbitPt, Fin.val_succ, Fin.val_castSucc, Function.iterate_succ_apply']

variable [Finite ι]

private theorem mem_periodicPts (π : Equiv.Perm ι) (w : ι) : w ∈ Function.periodicPts (⇑π) := by
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨i, hi, -, hw⟩ := Equiv.Perm.SameCycle.exists_pow_eq π (Equiv.Perm.SameCycle.refl π w)
  refine Function.mk_mem_periodicPts hi ?_
  show (⇑π)^[i] w = w
  rw [← Equiv.Perm.coe_pow]
  exact hw

private theorem orbitLen_succ (π : Equiv.Perm ι) (o : Quotient (orbitSetoid π)) :
    orbitLen π o + 1 = Function.minimalPeriod (⇑π) o.out :=
  Nat.succ_pred_eq_of_pos (Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts π o.out))

private theorem apply_orbitPt_last (π : Equiv.Perm ι) (o : Quotient (orbitSetoid π)) :
    π (orbitPt π o (Fin.last _)) = orbitPt π o 0 := by
  simp only [orbitPt, Fin.val_last, Fin.val_zero, Function.iterate_zero, id]
  rw [← Function.iterate_succ_apply' (⇑π)]
  have h := Function.iterate_minimalPeriod (f := ⇑π) (x := o.out)
  rwa [← orbitLen_succ π o] at h

private theorem orbitPt_injective (π : Equiv.Perm ι) :
    Function.Injective fun p : Σ o : Quotient (orbitSetoid π), Fin (orbitLen π o + 1) => orbitPt π p.1 p.2 := by
  rintro ⟨o, k⟩ ⟨o', k'⟩ h
  simp only [orbitPt] at h
  have ho : o = o' := by
    rw [← o.out_eq, ← o'.out_eq]
    apply Quotient.sound
    show π.SameCycle o.out o'.out
    have h1 : π.SameCycle o.out ((⇑π)^[k] o.out) := by
      rw [← Equiv.Perm.coe_pow]
      exact (Equiv.Perm.sameCycle_pow_left.mpr (Equiv.Perm.SameCycle.refl π _)).symm
    have h2 : π.SameCycle o'.out ((⇑π)^[k'] o'.out) := by
      rw [← Equiv.Perm.coe_pow]
      exact (Equiv.Perm.sameCycle_pow_left.mpr (Equiv.Perm.SameCycle.refl π _)).symm
    exact h1.trans (h ▸ h2.symm)
  subst ho
  have hk : (k : ℕ) = k' := by
    have hk1 : (k : ℕ) < Function.minimalPeriod (⇑π) o.out := orbitLen_succ π o ▸ k.isLt
    have hk2 : (k' : ℕ) < Function.minimalPeriod (⇑π) o.out := orbitLen_succ π o ▸ k'.isLt
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hk1 hk2).mp h
  rw [Fin.ext hk]

private theorem orbitPt_surjective (π : Equiv.Perm ι) :
    Function.Surjective fun p : Σ o : Quotient (orbitSetoid π), Fin (orbitLen π o + 1) => orbitPt π p.1 p.2 := by
  classical
  haveI := Fintype.ofFinite ι
  intro w
  set o : Quotient (orbitSetoid π) := Quotient.mk (orbitSetoid π) w with ho
  have hrel : π.SameCycle o.out w := Quotient.exact (s := orbitSetoid π) (by rw [o.out_eq])
  obtain ⟨i, -, -, hi⟩ := Equiv.Perm.SameCycle.exists_pow_eq π hrel
  refine ⟨⟨o, ⟨i % Function.minimalPeriod (⇑π) o.out, ?_⟩⟩, ?_⟩
  · rw [orbitLen_succ]
    exact Nat.mod_lt _ (Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts π _))
  · show (⇑π)^[i % Function.minimalPeriod (⇑π) o.out] o.out = w
    rw [Function.iterate_mod_minimalPeriod_eq, ← Equiv.Perm.coe_pow]
    exact hi

private noncomputable def orbitIndex (π : Equiv.Perm ι) :
    (Σ o : Quotient (orbitSetoid π), Fin (orbitLen π o + 1)) ≃ ι :=
  Equiv.ofBijective _ ⟨orbitPt_injective π, orbitPt_surjective π⟩

private theorem orbitIndex_apply (π : Equiv.Perm ι) (o : Quotient (orbitSetoid π)) (k : Fin (orbitLen π o + 1)) :
    orbitIndex π ⟨o, k⟩ = orbitPt π o k :=
  rfl

private noncomputable def orbitEquiv (π : Equiv.Perm ι) :
    (ι → H) ≃ₜ* ∀ o : Quotient (orbitSetoid π), Fin (orbitLen π o + 1) → H where
  toFun y o k := y (orbitPt π o k)
  invFun Y w := Y ((orbitIndex π).symm w).1 ((orbitIndex π).symm w).2
  left_inv y := by
    funext w
    show y (orbitIndex π ((orbitIndex π).symm w)) = y w
    rw [Equiv.apply_symm_apply]
  right_inv Y := by
    funext o k
    show Y ((orbitIndex π).symm (orbitIndex π ⟨o, k⟩)).1 ((orbitIndex π).symm (orbitIndex π ⟨o, k⟩)).2 = Y o k
    rw [Equiv.symm_apply_apply]
  map_mul' y z := rfl
  continuous_toFun := continuous_pi fun o => continuous_pi fun k => continuous_apply _
  continuous_invFun := continuous_pi fun w => (continuous_apply _).comp (continuous_apply _)

private theorem orbitEquiv_apply (π : Equiv.Perm ι) (y : ι → H) (o : Quotient (orbitSetoid π))
    (k : Fin (orbitLen π o + 1)) : orbitEquiv π y o k = y (orbitPt π o k) :=
  rfl

private theorem orbitEquiv_permTwist (π : Equiv.Perm ι) (a : ι → (H ≃ₜ* H)) (y : ι → H) :
    orbitEquiv π (permTwist π a y) =
      piTwist (fun o => stepTwist fun k => a (orbitPt π o k)) (orbitEquiv (H := H) π y) := by
  funext o k
  rw [orbitEquiv_apply, permTwist_apply, piTwist_apply]
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [stepTwist_last, orbitEquiv_apply, apply_orbitPt_last]
  · rw [stepTwist_castSucc, orbitEquiv_apply, orbitPt_succ]

variable [IsTopologicalGroup H]

private theorem isTwistedProper_permTwist (π : Equiv.Perm ι) (a : ι → (H ≃ₜ* H)) (δ : ι → H)
    (h : ∀ o : Quotient (orbitSetoid π),
      IsTwistedProper (closing fun k => a (orbitPt π o k)).toMonoidHom
        (cycleNorm (accumEquiv (fun k => a (orbitPt π o k)) fun k => δ (orbitPt π o k)))) :
    IsTwistedProper (permTwist π a) δ := by
  have h1 : IsTwistedProper (piTwist fun o => stepTwist fun k => a (orbitPt π o k)) (orbitEquiv π δ) :=
    isTwistedProper_piTwist _ _ fun o => isTwistedProper_stepTwist _ _ (h o)
  have h2 := isTwistedProper_of_continuousMulEquiv (orbitEquiv (H := H) π).symm _ (permTwist π a)
    (fun Y => by
      apply (orbitEquiv (H := H) π).injective
      rw [orbitEquiv_permTwist, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply])
    _ h1
  simpa using h2

end Orbits

section Strings

variable {ι : Type*} {H : Type*} [Group H] [TopologicalSpace H]

omit [TopologicalSpace H] in

private theorem twistedString_add {G : Type*} [Group G] (f : G →* G) (δ : G) (p q : ℕ) :
    SectionFunctions.twistedString f δ (p + q) =
      SectionFunctions.twistedString f δ p * (⇑f)^[p] (SectionFunctions.twistedString f δ q) := by
  induction q with
  | zero => simp [SectionFunctions.twistedString_zero]
  | succ q ih =>
    rw [← add_assoc, SectionFunctions.twistedString_succ, ih, SectionFunctions.twistedString_succ,
      iterate_map_mul, Function.iterate_add_apply, mul_assoc]

variable (π : Equiv.Perm ι) (a : ι → (H ≃ₜ* H)) (o : Quotient (orbitSetoid π))

private theorem permTwist_iterate_apply_orbitPt_zero (y : ι → H) (j : Fin (orbitLen π o + 1)) :
    (⇑(permTwist π a))^[j] y (orbitPt π o 0) = accum (fun k => a (orbitPt π o k)) j (y (orbitPt π o j)) := by
  induction j using Fin.induction generalizing y with
  | zero => rw [Fin.val_zero, Function.iterate_zero, id, accum_zero]; rfl
  | succ j ih =>
    rw [Fin.val_castSucc] at ih
    rw [Fin.val_succ, Function.iterate_succ_apply, ih, permTwist_apply, ← orbitPt_succ, accum_succ]
    rfl

private theorem cycleNorm_accumEquiv_eq (δ : ι → H) :
    cycleNorm (accumEquiv (fun k => a (orbitPt π o k)) fun k => δ (orbitPt π o k)) =
      SectionFunctions.twistedString (permTwist π a) δ (orbitLen π o + 1) (orbitPt π o 0) := by
  set t := accumEquiv (fun k => a (orbitPt π o k)) fun k => δ (orbitPt π o k) with ht
  have ht' : ∀ k, t k = (⇑(permTwist π a))^[k] δ (orbitPt π o 0) := fun k =>
    (permTwist_iterate_apply_orbitPt_zero π a o δ k).symm
  have hpart : ∀ i : Fin (orbitLen π o + 1), Fin.partialProd (Fin.init t) i =
      SectionFunctions.twistedString (permTwist π a) δ i (orbitPt π o 0) := by
    intro i
    induction i using Fin.induction with
    | zero => rw [Fin.partialProd_zero, Fin.val_zero, SectionFunctions.twistedString_zero]; rfl
    | succ j ih =>
      rw [partialProd_init_succ, ih, Fin.val_succ, SectionFunctions.twistedString_succ, Pi.mul_apply, ht',
        Fin.val_castSucc]
  rw [cycleNorm, hpart, ht', Fin.val_last, SectionFunctions.twistedString_succ, Pi.mul_apply]

variable [Finite ι]

private theorem permTwist_iterate_period (y : ι → H) :
    (⇑(permTwist π a))^[orbitLen π o + 1] y (orbitPt π o 0) =
      closing (fun k => a (orbitPt π o k)) (y (orbitPt π o 0)) := by
  have h := permTwist_iterate_apply_orbitPt_zero π a o (permTwist π a y) (Fin.last _)
  rw [Fin.val_last] at h
  rw [Function.iterate_succ_apply, h, permTwist_apply, apply_orbitPt_last]
  rfl

private theorem permTwist_iterate_mul_period (y : ι → H) (c : ℕ) :
    (⇑(permTwist π a))^[c * (orbitLen π o + 1)] y (orbitPt π o 0) =
      (⇑(closing fun k => a (orbitPt π o k)))^[c] (y (orbitPt π o 0)) := by
  induction c generalizing y with
  | zero => simp
  | succ c ih =>
    rw [Nat.succ_mul, Function.iterate_add_apply, ih, permTwist_iterate_period, Function.iterate_succ_apply]

private theorem twistedString_permTwist_apply_orbitPt_zero (δ : ι → H) (c : ℕ) :
    SectionFunctions.twistedString (permTwist π a) δ (c * (orbitLen π o + 1)) (orbitPt π o 0) =
      SectionFunctions.twistedString (closing fun k => a (orbitPt π o k)).toMonoidHom
        (cycleNorm (accumEquiv (fun k => a (orbitPt π o k)) fun k => δ (orbitPt π o k))) c := by
  induction c with
  | zero => rw [zero_mul, SectionFunctions.twistedString_zero, SectionFunctions.twistedString_zero]; rfl
  | succ c ih =>
    rw [Nat.succ_mul, twistedString_add, Pi.mul_apply, ih, permTwist_iterate_mul_period,
      ← cycleNorm_accumEquiv_eq, SectionFunctions.twistedString_succ, MulEquiv.coe_toMonoidHom]
    rfl

end Strings

section ClosingTwist

variable {F : Type*} [CommRing F] [TopologicalSpace F]

private theorem exists_closing_eq_map {m : ℕ} (a : Fin (m + 1) → (GL (Fin 2) F ≃ₜ* GL (Fin 2) F))
    (ha : ∀ k, ∃ r : F →+* F, Continuous r ∧ ∀ g, a k g = Matrix.GeneralLinearGroup.map r g) :
    ∃ r : F →+* F, Continuous r ∧ ∀ g, closing a g = Matrix.GeneralLinearGroup.map r g := by
  have key : ∀ j : Fin (m + 1),
      ∃ r : F →+* F, Continuous r ∧ ∀ g, accum a j g = Matrix.GeneralLinearGroup.map r g := by
    intro j
    induction j using Fin.induction with
    | zero =>
      refine ⟨RingHom.id F, continuous_id, fun g => ?_⟩
      rw [accum_zero]
      exact Units.ext (Matrix.ext fun _ _ => rfl)
    | succ j ih =>
      obtain ⟨r, hr, hacc⟩ := ih
      obtain ⟨s, hs, hstep⟩ := ha j.castSucc
      refine ⟨r.comp s, hr.comp hs, fun g => ?_⟩
      rw [accum_succ]
      show accum a j.castSucc (a j.castSucc g) = _
      rw [hstep, hacc]
      exact Units.ext (Matrix.ext fun _ _ => rfl)
  obtain ⟨r, hr, hacc⟩ := key (Fin.last m)
  obtain ⟨s, hs, hstep⟩ := ha (Fin.last m)
  refine ⟨r.comp s, hr.comp hs, fun g => ?_⟩
  show accum a (Fin.last m) (a (Fin.last m) g) = _
  rw [hstep, hacc]
  exact Units.ext (Matrix.ext fun _ _ => rfl)

omit [TopologicalSpace F] in
private theorem coe_iterate_glMap_apply (r : F →+* F) (i : ℕ) (g : GL (Fin 2) F) (p q : Fin 2) :
    (((⇑(Matrix.GeneralLinearGroup.map r))^[i] g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) p q =
      (⇑r)^[i] ((g : Matrix (Fin 2) (Fin 2) F) p q) := by
  induction i generalizing g with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

end ClosingTwist

section Extraction

variable {F : Type*} [Field F]

private theorem iterate_eq_self_of_forall_iterate_glMap (r : F →+* F) (c : ℕ)
    (h : ∀ g : GL (Fin 2) F, (⇑(Matrix.GeneralLinearGroup.map r))^[c] g = g) (x : F) : (⇑r)^[c] x = x := by
  have hdet : (!![(1 : F), x; 0, 1] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simp
  have hg := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1)
    (h (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet))
  simpa [coe_iterate_glMap_apply] using hg

end Extraction

section PermDescent

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {ι : Type*} [Finite ι]

private theorem isTwistedProper_permTwist_of_forall_glMap (π : Equiv.Perm ι)
    (a : ι → (GL (Fin 2) F ≃ₜ* GL (Fin 2) F))
    (ha : ∀ w, ∃ r : F →+* F, Continuous r ∧ ∀ g, a w g = Matrix.GeneralLinearGroup.map r g)
    (δ : ι → GL (Fin 2) F) (n : ℕ) (hn : ∀ w, (⇑π)^[n] w = w)
    (hreg : ∀ w, AutomorphicForm.IsRegularSemisimple (SectionFunctions.twistedString (permTwist π a) δ n w))
    (hper : ∀ y : ι → GL (Fin 2) F, (⇑(permTwist π a))^[n] y = y)
    (hF : ∀ r : F →+* F, Continuous r → ∀ c : ℕ, (∀ x, (⇑r)^[c] x = x) → ∀ δ' : GL (Fin 2) F,
      AutomorphicForm.IsRegularSemisimple
        (SectionFunctions.twistedString (Matrix.GeneralLinearGroup.map r) δ' c) →
      IsTwistedProper (Matrix.GeneralLinearGroup.map r) δ') :
    IsTwistedProper (permTwist π a) δ := by
  refine isTwistedProper_permTwist π a δ fun o => ?_
  obtain ⟨r, hr, hcl⟩ := exists_closing_eq_map (fun k => a (orbitPt π o k)) fun k => ha _
  have hmh : (closing fun k => a (orbitPt π o k)).toMonoidHom = Matrix.GeneralLinearGroup.map r :=
    MonoidHom.ext hcl
  obtain ⟨c, hc⟩ : orbitLen π o + 1 ∣ n := by
    rw [orbitLen_succ]
    exact Function.IsPeriodicPt.minimalPeriod_dvd (hn _)
  have hcn : c * (orbitLen π o + 1) = n := by rw [hc, mul_comm]
  rw [hmh]
  refine hF r hr c (fun x => ?_) _ ?_
  · refine iterate_eq_self_of_forall_iterate_glMap r c (fun g => ?_) x
    have h1 := permTwist_iterate_mul_period π a o (fun _ => g) c
    rw [hcn, hper] at h1
    have h2 : g = (⇑(closing fun k => a (orbitPt π o k)))^[c] g := h1
    rw [show ⇑(closing fun k => a (orbitPt π o k)) = ⇑(Matrix.GeneralLinearGroup.map r) from funext hcl] at h2
    exact h2.symm
  · rw [← hmh, ← twistedString_permTwist_apply_orbitPt_zero, hcn]
    exact hreg _

end PermDescent

end SigmaCycleDescent

set_option autoImplicit false

open scoped TensorProduct

namespace SigmaCycleDescent

section SigmaInfty

variable {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)

private def placeComap (w : NumberField.InfinitePlace L) : NumberField.InfinitePlace L :=
  w.comap (σ : L →+* L)

private theorem placeComap_comap_algebraMap (w : NumberField.InfinitePlace L) :
    (placeComap σ w).comap (algebraMap K L) = w.comap (algebraMap K L) := by
  unfold placeComap
  rw [← NumberField.InfinitePlace.comap_comp]
  congr 1
  ext c
  exact σ.commutes c

private def sigmaWithAbs (w : NumberField.InfinitePlace L) :
    WithAbs (placeComap σ w).1 →+* WithAbs w.1 :=
  WithAbs.map (placeComap σ w).1 w.1 (σ : L →+* L)

private theorem norm_sigmaWithAbs (w : NumberField.InfinitePlace L) (x : WithAbs (placeComap σ w).1) :
    ‖sigmaWithAbs σ w x‖ = ‖x‖ :=
  rfl

private theorem continuous_sigmaWithAbs (w : NumberField.InfinitePlace L) :
    Continuous (sigmaWithAbs σ w) :=
  AddMonoidHomClass.continuous_of_bound (sigmaWithAbs σ w) 1 fun x => by
    rw [norm_sigmaWithAbs, one_mul]

private noncomputable def sigmaHat (w : NumberField.InfinitePlace L) :
    (placeComap σ w).Completion →+* w.Completion :=
  (NumberField.InfinitePlace.Completion.equiv w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (sigmaWithAbs σ w) (continuous_sigmaWithAbs σ w)).comp
      (NumberField.InfinitePlace.Completion.equiv (placeComap σ w)).toRingHom)

private theorem continuous_sigmaHat (w : NumberField.InfinitePlace L) : Continuous (sigmaHat σ w) :=
  (NumberField.InfinitePlace.Completion.continuous_ofCompletion _).comp
    ((UniformSpace.Completion.continuous_map (f := sigmaWithAbs σ w)).comp
      (NumberField.InfinitePlace.Completion.continuous_toCompletion _))

private theorem sigmaHat_algebraMap (w : NumberField.InfinitePlace L) (l : L) :
    sigmaHat σ w (algebraMap L (placeComap σ w).Completion l) = algebraMap L w.Completion (σ l) :=
  NumberField.InfinitePlace.Completion.ext
    (UniformSpace.Completion.mapRingHom_coe (continuous_sigmaWithAbs σ w) (WithAbs.toAbs _ l))

private theorem sigmaTensor_tmul' (l : L) (x : NumberField.InfiniteAdeleRing K) :
    AutomorphicForm.sigmaTensor K L (NumberField.InfiniteAdeleRing K) σ (l ⊗ₜ[K] x) = σ l ⊗ₜ[K] x := by
  simp [AutomorphicForm.sigmaTensor]

private def sigmaInvWithAbs (w : NumberField.InfinitePlace L) : WithAbs w.1 →+* WithAbs (placeComap σ w).1 :=
  WithAbs.map w.1 (placeComap σ w).1 (σ.symm : L →+* L)

private theorem norm_sigmaInvWithAbs (w : NumberField.InfinitePlace L) (x : WithAbs w.1) :
    ‖sigmaInvWithAbs σ w x‖ = ‖x‖ := by
  show (placeComap σ w) ((σ.symm : L →+* L) (WithAbs.ofAbs x)) = w (WithAbs.ofAbs x)
  rw [placeComap, NumberField.InfinitePlace.comap_apply]
  exact congrArg w (σ.apply_symm_apply _)

private theorem continuous_sigmaInvWithAbs (w : NumberField.InfinitePlace L) :
    Continuous (sigmaInvWithAbs σ w) :=
  AddMonoidHomClass.continuous_of_bound (sigmaInvWithAbs σ w) 1 fun x => by
    rw [norm_sigmaInvWithAbs, one_mul]

private noncomputable def sigmaHatInv (w : NumberField.InfinitePlace L) :
    w.Completion →+* (placeComap σ w).Completion :=
  (NumberField.InfinitePlace.Completion.equiv (placeComap σ w)).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (sigmaInvWithAbs σ w) (continuous_sigmaInvWithAbs σ w)).comp
      (NumberField.InfinitePlace.Completion.equiv w).toRingHom)

private theorem continuous_sigmaHatInv (w : NumberField.InfinitePlace L) : Continuous (sigmaHatInv σ w) :=
  (NumberField.InfinitePlace.Completion.continuous_ofCompletion _).comp
    ((UniformSpace.Completion.continuous_map (f := sigmaInvWithAbs σ w)).comp
      (NumberField.InfinitePlace.Completion.continuous_toCompletion _))

private theorem sigmaHatInv_algebraMap (w : NumberField.InfinitePlace L) (l : L) :
    sigmaHatInv σ w (algebraMap L w.Completion l) = algebraMap L (placeComap σ w).Completion (σ.symm l) :=
  NumberField.InfinitePlace.Completion.ext
    (UniformSpace.Completion.mapRingHom_coe (continuous_sigmaInvWithAbs σ w) (WithAbs.toAbs _ l))

private theorem sigmaHat_comp_sigmaHatInv (w : NumberField.InfinitePlace L) :
    (sigmaHat σ w).comp (sigmaHatInv σ w) = RingHom.id w.Completion := by
  refine RingHom.ext (congrFun ((M4aHerbrand.ArchSemilocal.denseRange_algebraMap_completion w).equalizer
    ((continuous_sigmaHat σ w).comp (continuous_sigmaHatInv σ w)) continuous_id ?_))
  funext l
  simp only [Function.comp_apply, RingHom.comp_apply, RingHom.id_apply, sigmaHatInv_algebraMap, sigmaHat_algebraMap,
    AlgEquiv.apply_symm_apply]

private theorem sigmaHatInv_comp_sigmaHat (w : NumberField.InfinitePlace L) :
    (sigmaHatInv σ w).comp (sigmaHat σ w) = RingHom.id (placeComap σ w).Completion := by
  refine RingHom.ext (congrFun
    ((M4aHerbrand.ArchSemilocal.denseRange_algebraMap_completion (placeComap σ w)).equalizer
    ((continuous_sigmaHatInv σ w).comp (continuous_sigmaHat σ w)) continuous_id ?_))
  funext l
  simp only [Function.comp_apply, RingHom.comp_apply, RingHom.id_apply, sigmaHat_algebraMap, sigmaHatInv_algebraMap,
    AlgEquiv.symm_apply_apply]

private noncomputable def sigmaHatEquiv (w : NumberField.InfinitePlace L) :
    (placeComap σ w).Completion ≃+* w.Completion :=
  RingEquiv.ofRingHom (sigmaHat σ w) (sigmaHatInv σ w) (sigmaHat_comp_sigmaHatInv σ w)
    (sigmaHatInv_comp_sigmaHat σ w)

private theorem coe_sigmaHatEquiv (w : NumberField.InfinitePlace L) : ⇑(sigmaHatEquiv σ w) = ⇑(sigmaHat σ w) :=
  rfl

private theorem coe_sigmaHatEquiv_symm (w : NumberField.InfinitePlace L) :
    ⇑(sigmaHatEquiv σ w).symm = ⇑(sigmaHatInv σ w) :=
  rfl

private theorem continuous_sigmaHatEquiv (w : NumberField.InfinitePlace L) : Continuous (sigmaHatEquiv σ w) :=
  continuous_sigmaHat σ w

private theorem continuous_sigmaHatEquiv_symm (w : NumberField.InfinitePlace L) :
    Continuous (sigmaHatEquiv σ w).symm :=
  continuous_sigmaHatInv σ w

private theorem infiniteAdeleRing_zero_apply (w : NumberField.InfinitePlace L) :
    (0 : NumberField.InfiniteAdeleRing L) w = 0 :=
  rfl

private theorem infiniteAdeleRing_add_apply (a b : NumberField.InfiniteAdeleRing L) (w : NumberField.InfinitePlace L) :
    (a + b) w = a w + b w :=
  rfl

private theorem infiniteAdeleRing_mul_apply (a b : NumberField.InfiniteAdeleRing L) (w : NumberField.InfinitePlace L) :
    (a * b) w = a w * b w :=
  rfl

variable [NumberField K] [NumberField L]

open scoped NumberField.LiesOver

omit [NumberField K] [NumberField L] in

private theorem sigmaHat_algebraMap_completion (w : NumberField.InfinitePlace L)
    {v : NumberField.InfinitePlace K} [w.1.LiesOver v.1] [(placeComap σ w).1.LiesOver v.1]
    (c : v.Completion) :
    sigmaHat σ w (algebraMap v.Completion (placeComap σ w).Completion c) =
      algebraMap v.Completion w.Completion c := by
  have hdense := M4aHerbrand.ArchSemilocal.denseRange_algebraMap_completion v
  have h1 : Continuous fun c : v.Completion =>
      sigmaHat σ w (algebraMap v.Completion (placeComap σ w).Completion c) :=
    (continuous_sigmaHat σ w).comp (M4aHerbrand.ArchSemilocal.continuous_algebraMap_completion v _)
  have h2 : Continuous fun c : v.Completion => algebraMap v.Completion w.Completion c :=
    M4aHerbrand.ArchSemilocal.continuous_algebraMap_completion v w
  refine congrFun (hdense.equalizer h1 h2 ?_) c
  funext a
  simp only [Function.comp_apply, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply K L (placeComap σ w).Completion a,
    IsScalarTower.algebraMap_apply K L w.Completion a, sigmaHat_algebraMap, σ.commutes]

private theorem conorm_apply_place (x : NumberField.InfiniteAdeleRing K) (w : NumberField.InfinitePlace L)
    {v : NumberField.InfinitePlace K} (hv : w.comap (algebraMap K L) = v) [w.1.LiesOver v.1] :
    (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).conorm x w =
      algebraMap v.Completion w.Completion (x v) := by
  subst hv
  show M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w
      ((x (w.comap (algebraMap K L))) ⊗ₜ[K] (1 : L)) = _
  rw [M4aHerbrand.ArchSemilocal.psiFactor_tmul, map_one, mul_one]

private theorem archIdent_tmul (l : L) (x : NumberField.InfiniteAdeleRing K) :
    AutomorphicForm.archIdent K L (l ⊗ₜ[K] x) =
      (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).conorm x *
        algebraMap L (NumberField.InfiniteAdeleRing L) l := by
  show (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv
      (Algebra.TensorProduct.comm K L (NumberField.InfiniteAdeleRing K) (l ⊗ₜ[K] x)) = _
  rw [Algebra.TensorProduct.comm_tmul]
  have h : (x ⊗ₜ[K] l : NumberField.InfiniteAdeleRing K ⊗[K] L) = (x ⊗ₜ[K] (1 : L)) * ((1 : _) ⊗ₜ[K] l) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeRingEquiv_tmul_one,
    FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeRingEquiv_one_tmul]

private theorem archIdent_sigmaTensor_apply (z : L ⊗[K] NumberField.InfiniteAdeleRing K)
    (w : NumberField.InfinitePlace L) :
    AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (NumberField.InfiniteAdeleRing K) σ z) w =
      sigmaHat σ w (AutomorphicForm.archIdent K L z (placeComap σ w)) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, infiniteAdeleRing_zero_apply, infiniteAdeleRing_zero_apply, map_zero]
  | add a b ha hb =>
    rw [map_add, map_add, infiniteAdeleRing_add_apply, map_add, infiniteAdeleRing_add_apply, map_add, ha, hb]
  | tmul l x =>
    haveI : w.1.LiesOver (w.comap (algebraMap K L)).1 := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq rfl
    haveI : (placeComap σ w).1.LiesOver (w.comap (algebraMap K L)).1 :=
      M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq (placeComap_comap_algebraMap σ w)
    rw [sigmaTensor_tmul', archIdent_tmul, archIdent_tmul, infiniteAdeleRing_mul_apply,
      infiniteAdeleRing_mul_apply, map_mul,
      FLT.InfiniteAdeleBaseChange.algebraMap_infiniteAdeleRing_apply,
      FLT.InfiniteAdeleBaseChange.algebraMap_infiniteAdeleRing_apply, sigmaHat_algebraMap,
      conorm_apply_place x w rfl, conorm_apply_place x (placeComap σ w) (placeComap_comap_algebraMap σ w),
      sigmaHat_algebraMap_completion]

end SigmaInfty

section Factors

variable {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)

private noncomputable def sigmaFactors :
    (∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion) →*
      ∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion :=
  MonoidHom.pi fun w => (Matrix.GeneralLinearGroup.map (sigmaHat σ w)).comp
    (Pi.evalMonoidHom (fun w : NumberField.InfinitePlace L => GL (Fin 2) w.Completion) (placeComap σ w))

private theorem sigmaFactors_apply (y : ∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion)
    (w : NumberField.InfinitePlace L) :
    sigmaFactors σ y w = Matrix.GeneralLinearGroup.map (sigmaHat σ w) (y (placeComap σ w)) :=
  rfl

variable [NumberField K] [NumberField L]

private theorem archFactors_sigmaGL (g : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K)) :
    TwistedOrbitProperness.archFactors K L (AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ g) =
      sigmaFactors σ (TwistedOrbitProperness.archFactors K L g) := by
  funext w
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [TwistedOrbitProperness.archFactors_apply_coe, sigmaFactors_apply, SectionFunctions.coe_glMap,
    Matrix.map_apply, TwistedOrbitProperness.archFactors_apply_coe, ← archIdent_sigmaTensor_apply]
  rfl

private theorem isTwistedProper_sigmaGL_of_sigmaFactors (δ : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K))
    (h : IsTwistedProper (sigmaFactors σ) (TwistedOrbitProperness.archFactors K L δ)) :
    IsTwistedProper (AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ) δ := by
  have h2 := isTwistedProper_of_continuousMulEquiv (TwistedOrbitProperness.archFactors K L).symm _
    (AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ)
    (fun y => by
      apply (TwistedOrbitProperness.archFactors K L).injective
      rw [archFactors_sigmaGL, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply])
    _ h
  simpa using h2

private theorem archFactors_normString (δ : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K)) :
    TwistedOrbitProperness.archFactors K L (AutomorphicForm.normString K L (NumberField.InfiniteAdeleRing K) σ δ) =
      SectionFunctions.twistedString (sigmaFactors σ) (TwistedOrbitProperness.archFactors K L δ)
        (Module.finrank K L) :=
  SectionFunctions.map_twistedString (TwistedOrbitProperness.archFactors K L).toMonoidHom
    (AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ) (sigmaFactors σ) (archFactors_sigmaGL σ) δ
    (Module.finrank K L)

private theorem archFactors_apply_eq_map (g : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K))
    (w : NumberField.InfinitePlace L) :
    TwistedOrbitProperness.archFactors K L g w = Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun w : NumberField.InfinitePlace L => w.Completion) w).comp
        (AutomorphicForm.archIdent K L)) g :=
  Units.ext (Matrix.ext fun i j => by
    rw [TwistedOrbitProperness.archFactors_apply_coe, SectionFunctions.coe_glMap, Matrix.map_apply]
    rfl)

private theorem isRegularSemisimple_archFactors {g : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K)}
    (hg : AutomorphicForm.IsRegularSemisimple g) (w : NumberField.InfinitePlace L) :
    AutomorphicForm.IsRegularSemisimple (TwistedOrbitProperness.archFactors K L g w) := by
  rw [archFactors_apply_eq_map]
  exact SectionFunctions.isRegularSemisimple_glMap _ hg

end Factors

end SigmaCycleDescent

namespace SigmaCycleDescent

section ModelFields

private theorem iterate_two_mul_apply {α : Type*} {f : α → α} (hf : ∀ x, f (f x) = x) (x : α) (m : ℕ) :
    f^[2 * m] x = x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : f^[2] x = x := hf x
    rw [mul_add, mul_one, Function.iterate_add_apply, h2, ih]

private theorem isTwistedProper_glMap_of_forall_eq {F : Type*} [Field F] [CharZero F] [TopologicalSpace F]
    {ρ : F →+* F} (hρ : ∀ a, ρ a = a) {δ' : GL (Fin 2) F} {k : ℕ}
    (hreg : AutomorphicForm.IsRegularSemisimple
      (SectionFunctions.twistedString (Matrix.GeneralLinearGroup.map ρ) δ' k))
    (hF : ∀ y : GL (Fin 2) F, AutomorphicForm.IsRegularSemisimple y → IsTwistedProper (MonoidHom.id _) y) :
    IsTwistedProper (Matrix.GeneralLinearGroup.map ρ) δ' := by
  have hmap : ∀ g : GL (Fin 2) F, Matrix.GeneralLinearGroup.map ρ g = g :=
    SectionFunctions.glMap_eq_self_of_forall_eq hρ
  rw [SectionFunctions.twistedString_of_forall_eq hmap] at hreg
  have hid : Matrix.GeneralLinearGroup.map ρ = MonoidHom.id (GL (Fin 2) F) := MonoidHom.ext hmap
  rw [hid]
  exact hF δ' (isRegularSemisimple_of_pow hreg)

private theorem isTwistedProper_glMap_real (ρ : ℝ →+* ℝ) (k : ℕ) (δ' : GL (Fin 2) ℝ)
    (hreg : AutomorphicForm.IsRegularSemisimple
      (SectionFunctions.twistedString (Matrix.GeneralLinearGroup.map ρ) δ' k))
    (hR : ∀ δ' : GL (Fin 2) ℝ, AutomorphicForm.IsRegularSemisimple δ' → IsTwistedProper (MonoidHom.id _) δ') :
    IsTwistedProper (Matrix.GeneralLinearGroup.map ρ) δ' :=
  isTwistedProper_glMap_of_forall_eq (fun a => by rw [Subsingleton.elim ρ (RingHom.id ℝ)]; rfl) hreg hR

private theorem isTwistedProper_glMap_complex (ρ : ℂ →+* ℂ) (hρ : Continuous ρ) (k : ℕ)
    (hρk : ∀ x, (⇑ρ)^[k] x = x) (δ' : GL (Fin 2) ℂ)
    (hreg : AutomorphicForm.IsRegularSemisimple
      (SectionFunctions.twistedString (Matrix.GeneralLinearGroup.map ρ) δ' k))
    (hC : ∀ δ' : GL (Fin 2) ℂ, AutomorphicForm.IsRegularSemisimple δ' → IsTwistedProper (MonoidHom.id _) δ')
    (hconj : ∀ δ' : GL (Fin 2) ℂ,
      AutomorphicForm.IsRegularSemisimple (δ' * Matrix.GeneralLinearGroup.map (starRingEnd ℂ) δ') →
      IsTwistedProper (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) δ') :
    IsTwistedProper (Matrix.GeneralLinearGroup.map ρ) δ' := by
  rcases Complex.ringHom_eq_id_or_conj_of_continuous hρ with hid | hcj
  · exact isTwistedProper_glMap_of_forall_eq (fun a => by rw [hid]; rfl) hreg hC
  · subst hcj
    obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := by
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨m, by omega⟩
      · exfalso
        have hI := hρk Complex.I
        have h2 : (⇑(starRingEnd ℂ))^[k] Complex.I = starRingEnd ℂ Complex.I := by
          rw [hm, Function.iterate_add_apply, Function.iterate_one,
            iterate_two_mul_apply (fun z => Complex.conj_conj z)]
        rw [h2] at hI
        have him := congrArg Complex.im hI
        norm_num at him
    have hinv : ∀ g : GL (Fin 2) ℂ,
        Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (Matrix.GeneralLinearGroup.map (starRingEnd ℂ) g) = g :=
      SectionFunctions.glMap_glMap_eq_self_of_forall_eq fun z => Complex.conj_conj z
    rw [SectionFunctions.twistedString_two_mul hinv] at hreg
    exact hconj δ' (isRegularSemisimple_of_pow hreg)

end ModelFields

end SigmaCycleDescent

namespace SigmaCycleDescent

section ProductTwists

variable {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]

private theorem isTwistedProper_prodMap (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) {δ₁ : G₁} {δ₂ : G₂}
    (h₁ : IsTwistedProper θ₁ δ₁) (h₂ : IsTwistedProper θ₂ δ₂) : IsTwistedProper (θ₁.prodMap θ₂) (δ₁, δ₂) := by
  rw [isTwistedProper_iff] at h₁ h₂ ⊢
  intro C hC
  obtain ⟨D₁, hD₁, hfac₁⟩ := h₁ (Prod.fst '' C) (hC.image continuous_fst)
  obtain ⟨D₂, hD₂, hfac₂⟩ := h₂ (Prod.snd '' C) (hC.image continuous_snd)
  refine ⟨D₁ ×ˢ D₂, hD₁.prod hD₂, fun x hx => ?_⟩
  obtain ⟨t₁, ht₁, d₁, hd₁, htd₁⟩ := hfac₁ x.1 ⟨_, hx, rfl⟩
  obtain ⟨t₂, ht₂, d₂, hd₂, htd₂⟩ := hfac₂ x.2 ⟨_, hx, rfl⟩
  refine ⟨(t₁, t₂), ?_, (d₁, d₂), ⟨hd₁, hd₂⟩, Prod.ext htd₁ htd₂⟩
  rw [AutomorphicForm.mem_sigmaCentralizer_iff] at ht₁ ht₂ ⊢
  exact Prod.ext ht₁ ht₂

end ProductTwists

section SubtypePermutations

variable {α : Type*} {p : α → Prop}

private theorem coe_iterate_subtypePerm (f : Equiv.Perm α) (h : ∀ x, p (f x) ↔ p x) (n : ℕ) (x : {a // p a}) :
    (((⇑(f.subtypePerm h))^[n] x : {a // p a}) : α) = (⇑f)^[n] (x : α) := by
  induction n generalizing x with
  | zero => rfl
  | succ m ih => simp only [Function.iterate_succ_apply, ih, Equiv.Perm.subtypePerm_apply]

end SubtypePermutations

section PlacePermutation

variable {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)

private theorem one_ringHom : ((1 : L ≃ₐ[K] L) : L →+* L) = RingHom.id L :=
  RingHom.ext fun x => AlgEquiv.one_apply x

private theorem mul_ringHom (τ₁ τ₂ : L ≃ₐ[K] L) : ((τ₁ * τ₂ : L ≃ₐ[K] L) : L →+* L) = (τ₁ : L →+* L).comp τ₂ :=
  RingHom.ext fun x => AlgEquiv.mul_apply τ₁ τ₂ x

private theorem placeComap_placeComap_symm (w : NumberField.InfinitePlace L) :
    placeComap σ (placeComap σ.symm w) = w := by
  unfold placeComap
  rw [← NumberField.InfinitePlace.comap_comp]
  convert NumberField.InfinitePlace.comap_id w using 2
  exact RingHom.ext fun x => σ.symm_apply_apply x

private theorem placeComap_symm_placeComap (w : NumberField.InfinitePlace L) :
    placeComap σ.symm (placeComap σ w) = w := by
  unfold placeComap
  rw [← NumberField.InfinitePlace.comap_comp]
  convert NumberField.InfinitePlace.comap_id w using 2
  exact RingHom.ext fun x => σ.apply_symm_apply x

private noncomputable def placePerm : Equiv.Perm (NumberField.InfinitePlace L) where
  toFun := placeComap σ
  invFun := placeComap σ.symm
  left_inv := placeComap_symm_placeComap σ
  right_inv := placeComap_placeComap_symm σ

private theorem placePerm_apply (w : NumberField.InfinitePlace L) : placePerm σ w = placeComap σ w :=
  rfl

private theorem placePerm_iterate (n : ℕ) (w : NumberField.InfinitePlace L) :
    (⇑(placePerm σ))^[n] w = w.comap ((σ ^ n : L ≃ₐ[K] L) : L →+* L) := by
  induction n with
  | zero => rw [Function.iterate_zero, id_eq, pow_zero, one_ringHom, NumberField.InfinitePlace.comap_id]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, placePerm_apply]
    unfold placeComap
    rw [← NumberField.InfinitePlace.comap_comp, pow_succ, mul_ringHom]

private theorem placePerm_iterate_eq_self {n : ℕ} (hσ : σ ^ n = 1) (w : NumberField.InfinitePlace L) :
    (⇑(placePerm σ))^[n] w = w := by
  rw [placePerm_iterate, hσ, one_ringHom, NumberField.InfinitePlace.comap_id]

private theorem isReal_placeComap_iff (w : NumberField.InfinitePlace L) :
    (placeComap σ w).IsReal ↔ w.IsReal :=
  NumberField.InfinitePlace.isReal_comap_iff (σ : L ≃+* L)

private theorem isComplex_placeComap_iff (w : NumberField.InfinitePlace L) :
    (placeComap σ w).IsComplex ↔ w.IsComplex := by
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex, ← NumberField.InfinitePlace.not_isReal_iff_isComplex,
    isReal_placeComap_iff]

private noncomputable def realPerm : Equiv.Perm {w : NumberField.InfinitePlace L // w.IsReal} :=
  (placePerm σ).subtypePerm (isReal_placeComap_iff σ)

private noncomputable def complexPerm : Equiv.Perm {w : NumberField.InfinitePlace L // w.IsComplex} :=
  (placePerm σ).subtypePerm (isComplex_placeComap_iff σ)

private theorem realPerm_apply_coe (r : {w : NumberField.InfinitePlace L // w.IsReal}) :
    (realPerm σ r : NumberField.InfinitePlace L) = placeComap σ r :=
  rfl

private theorem complexPerm_apply_coe (c : {w : NumberField.InfinitePlace L // w.IsComplex}) :
    (complexPerm σ c : NumberField.InfinitePlace L) = placeComap σ c :=
  rfl

private theorem realPerm_iterate_eq_self {n : ℕ} (hσ : σ ^ n = 1) (r : {w : NumberField.InfinitePlace L // w.IsReal}) :
    (⇑(realPerm σ))^[n] r = r :=
  Subtype.ext (by rw [realPerm, coe_iterate_subtypePerm, placePerm_iterate_eq_self σ hσ])

private theorem complexPerm_iterate_eq_self {n : ℕ} (hσ : σ ^ n = 1)
    (c : {w : NumberField.InfinitePlace L // w.IsComplex}) : (⇑(complexPerm σ))^[n] c = c :=
  Subtype.ext (by rw [complexPerm, coe_iterate_subtypePerm, placePerm_iterate_eq_self σ hσ])

end PlacePermutation

section ModelIdentifications

variable {L : Type} [Field L]

private theorem continuous_ringEquivReal {w : NumberField.InfinitePlace L} (hw : w.IsReal) :
    Continuous (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) :=
  (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous

private theorem continuous_ringEquivReal_symm {w : NumberField.InfinitePlace L} (hw : w.IsReal) :
    Continuous (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm :=
  (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous

private theorem continuous_ringEquivComplex {w : NumberField.InfinitePlace L} (hw : w.IsComplex) :
    Continuous (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) :=
  (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).continuous

private theorem continuous_ringEquivComplex_symm {w : NumberField.InfinitePlace L} (hw : w.IsComplex) :
    Continuous (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm :=
  (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous

private noncomputable def glRealEquiv (r : {w : NumberField.InfinitePlace L // w.IsReal}) :
    GL (Fin 2) r.1.Completion ≃ₜ* GL (Fin 2) ℝ :=
  SectionFunctions.glContinuousMulEquiv (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal r.2)
    (continuous_ringEquivReal r.2) (continuous_ringEquivReal_symm r.2)

private noncomputable def glComplexEquiv (c : {w : NumberField.InfinitePlace L // w.IsComplex}) :
    GL (Fin 2) c.1.Completion ≃ₜ* GL (Fin 2) ℂ :=
  SectionFunctions.glContinuousMulEquiv (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex c.2)
    (continuous_ringEquivComplex c.2) (continuous_ringEquivComplex_symm c.2)

open scoped Classical in

private noncomputable def splitEquiv :
    (∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion) ≃ₜ*
      ({w : NumberField.InfinitePlace L // w.IsReal} → GL (Fin 2) ℝ) ×
        ({w : NumberField.InfinitePlace L // w.IsComplex} → GL (Fin 2) ℂ) where
  toFun y := (fun r => glRealEquiv r (y r.1), fun c => glComplexEquiv c (y c.1))
  invFun z w :=
    if h : w.IsReal then (glRealEquiv ⟨w, h⟩).symm (z.1 ⟨w, h⟩)
    else (glComplexEquiv ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.1 h⟩).symm
      (z.2 ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.1 h⟩)
  left_inv y := by
    funext w
    by_cases h : w.IsReal
    · simp [h]
    · simp [h]
  right_inv z := by
    refine Prod.ext (funext fun r => ?_) (funext fun c => ?_)
    · simp [r.2]
    · have hc : ¬ c.1.IsReal := NumberField.InfinitePlace.not_isReal_iff_isComplex.2 c.2
      simp [hc]
  map_mul' y z := by
    refine Prod.ext (funext fun r => ?_) (funext fun c => ?_) <;> simp
  continuous_toFun :=
    (continuous_pi fun r => (glRealEquiv r).continuous.comp (continuous_apply r.1)).prodMk
      (continuous_pi fun c => (glComplexEquiv c).continuous.comp (continuous_apply c.1))
  continuous_invFun := by
    refine continuous_pi fun w => ?_
    by_cases h : w.IsReal
    · simp only [dif_pos h]
      exact (glRealEquiv ⟨w, h⟩).symm.continuous.comp ((continuous_apply _).comp continuous_fst)
    · simp only [dif_neg h]
      exact (glComplexEquiv _).symm.continuous.comp ((continuous_apply _).comp continuous_snd)

private theorem splitEquiv_apply_fst' (y : ∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion)
    (r : {w : NumberField.InfinitePlace L // w.IsReal}) : (splitEquiv y).1 r = glRealEquiv r (y r.1) :=
  rfl

private theorem splitEquiv_apply_snd' (y : ∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion)
    (c : {w : NumberField.InfinitePlace L // w.IsComplex}) : (splitEquiv y).2 c = glComplexEquiv c (y c.1) :=
  rfl

private theorem splitEquiv_apply_fst (y : ∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion)
    (r : {w : NumberField.InfinitePlace L // w.IsReal}) :
    (splitEquiv y).1 r = Matrix.GeneralLinearGroup.map
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal r.2).toRingHom (y r.1) :=
  SectionFunctions.glContinuousMulEquiv_apply _ _ _ _

private theorem splitEquiv_apply_snd (y : ∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion)
    (c : {w : NumberField.InfinitePlace L // w.IsComplex}) :
    (splitEquiv y).2 c = Matrix.GeneralLinearGroup.map
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex c.2).toRingHom (y c.1) :=
  SectionFunctions.glContinuousMulEquiv_apply _ _ _ _

end ModelIdentifications

section ModelTwists

variable {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)

private noncomputable def rhoReal (r : {w : NumberField.InfinitePlace L // w.IsReal}) : ℝ ≃+* ℝ :=
  ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal ((isReal_placeComap_iff σ r.1).2 r.2)).symm.trans
    (sigmaHatEquiv σ r.1)).trans (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal r.2)

private noncomputable def rhoComplex (c : {w : NumberField.InfinitePlace L // w.IsComplex}) : ℂ ≃+* ℂ :=
  ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
    ((isComplex_placeComap_iff σ c.1).2 c.2)).symm.trans (sigmaHatEquiv σ c.1)).trans
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex c.2)

private theorem continuous_rhoReal (r : {w : NumberField.InfinitePlace L // w.IsReal}) : Continuous (rhoReal σ r) := by
  unfold rhoReal
  simp only [RingEquiv.coe_trans]
  exact (continuous_ringEquivReal r.2).comp
    ((continuous_sigmaHatEquiv σ r.1).comp (continuous_ringEquivReal_symm _))

private theorem continuous_rhoReal_symm (r : {w : NumberField.InfinitePlace L // w.IsReal}) :
    Continuous (rhoReal σ r).symm := by
  have h : ⇑(rhoReal σ r).symm = fun x =>
      NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal ((isReal_placeComap_iff σ r.1).2 r.2)
        ((sigmaHatEquiv σ r.1).symm
          ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal r.2).symm x)) := by
    funext x
    simp only [rhoReal, RingEquiv.symm_trans_apply, RingEquiv.symm_symm]
  rw [h]
  exact (continuous_ringEquivReal _).comp
    ((continuous_sigmaHatEquiv_symm σ r.1).comp (continuous_ringEquivReal_symm r.2))

private theorem continuous_rhoComplex (c : {w : NumberField.InfinitePlace L // w.IsComplex}) :
    Continuous (rhoComplex σ c) := by
  unfold rhoComplex
  simp only [RingEquiv.coe_trans]
  exact (continuous_ringEquivComplex c.2).comp
    ((continuous_sigmaHatEquiv σ c.1).comp (continuous_ringEquivComplex_symm _))

private theorem continuous_rhoComplex_symm (c : {w : NumberField.InfinitePlace L // w.IsComplex}) :
    Continuous (rhoComplex σ c).symm := by
  have h : ⇑(rhoComplex σ c).symm = fun x =>
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex ((isComplex_placeComap_iff σ c.1).2 c.2)
        ((sigmaHatEquiv σ c.1).symm
          ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex c.2).symm x)) := by
    funext x
    simp [rhoComplex]
  rw [h]
  exact (continuous_ringEquivComplex _).comp
    ((continuous_sigmaHatEquiv_symm σ c.1).comp (continuous_ringEquivComplex_symm c.2))

private noncomputable def aReal : {w : NumberField.InfinitePlace L // w.IsReal} → (GL (Fin 2) ℝ ≃ₜ* GL (Fin 2) ℝ) :=
  fun r => SectionFunctions.glContinuousMulEquiv (rhoReal σ r) (continuous_rhoReal σ r) (continuous_rhoReal_symm σ r)

private noncomputable def aComplex :
    {w : NumberField.InfinitePlace L // w.IsComplex} → (GL (Fin 2) ℂ ≃ₜ* GL (Fin 2) ℂ) :=
  fun c => SectionFunctions.glContinuousMulEquiv (rhoComplex σ c) (continuous_rhoComplex σ c)
    (continuous_rhoComplex_symm σ c)

end ModelTwists

end SigmaCycleDescent

namespace SigmaCycleDescent

section SplitSemiconjugacy

variable {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)

private theorem rhoReal_apply_ringEquiv (r : {w : NumberField.InfinitePlace L // w.IsReal})
    (x : (placeComap σ r.1).Completion) :
    rhoReal σ r (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal ((isReal_placeComap_iff σ r.1).2 r.2) x) =
      NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal r.2 (sigmaHat σ r.1 x) := by
  simp only [rhoReal, RingEquiv.trans_apply, RingEquiv.symm_apply_apply, coe_sigmaHatEquiv]

private theorem rhoComplex_apply_ringEquiv (c : {w : NumberField.InfinitePlace L // w.IsComplex})
    (x : (placeComap σ c.1).Completion) :
    rhoComplex σ c (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        ((isComplex_placeComap_iff σ c.1).2 c.2) x) =
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex c.2 (sigmaHat σ c.1 x) := by
  simp only [rhoComplex, RingEquiv.trans_apply, RingEquiv.symm_apply_apply, coe_sigmaHatEquiv]

private theorem splitEquiv_sigmaFactors (y : ∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion) :
    splitEquiv (sigmaFactors σ y) =
      (permTwist (realPerm σ) (aReal σ)).prodMap (permTwist (complexPerm σ) (aComplex σ)) (splitEquiv y) := by
  refine Prod.ext (funext fun r => ?_) (funext fun c => ?_)
  · rw [MonoidHom.coe_prodMap, Prod.map_fst, permTwist_apply, splitEquiv_apply_fst', splitEquiv_apply_fst',
      sigmaFactors_apply]
    show glRealEquiv r (Matrix.GeneralLinearGroup.map (sigmaHat σ r.1) (y (placeComap σ r.1))) =
      aReal σ r (glRealEquiv ⟨placeComap σ r.1, (isReal_placeComap_iff σ r.1).2 r.2⟩ (y (placeComap σ r.1)))
    simp only [glRealEquiv, aReal, SectionFunctions.glContinuousMulEquiv_apply]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    simp only [SectionFunctions.coe_glMap, Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      rhoReal_apply_ringEquiv]
  · rw [MonoidHom.coe_prodMap, Prod.map_snd, permTwist_apply, splitEquiv_apply_snd', splitEquiv_apply_snd',
      sigmaFactors_apply]
    show glComplexEquiv c (Matrix.GeneralLinearGroup.map (sigmaHat σ c.1) (y (placeComap σ c.1))) =
      aComplex σ c
        (glComplexEquiv ⟨placeComap σ c.1, (isComplex_placeComap_iff σ c.1).2 c.2⟩ (y (placeComap σ c.1)))
    simp only [glComplexEquiv, aComplex, SectionFunctions.glContinuousMulEquiv_apply]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    simp only [SectionFunctions.coe_glMap, Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      rhoComplex_apply_ringEquiv]

end SplitSemiconjugacy

end SigmaCycleDescent

namespace SigmaCycleDescent

section SplitStrings

variable {K L : Type} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)

private theorem splitEquiv_twistedString (Y : ∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion) (k : ℕ) :
    splitEquiv (SectionFunctions.twistedString (sigmaFactors σ) Y k) =
      SectionFunctions.twistedString
        ((permTwist (realPerm σ) (aReal σ)).prodMap (permTwist (complexPerm σ) (aComplex σ))) (splitEquiv Y) k :=
  SectionFunctions.map_twistedString (splitEquiv (L := L)).toMonoidHom (sigmaFactors σ)
    ((permTwist (realPerm σ) (aReal σ)).prodMap (permTwist (complexPerm σ) (aComplex σ))) (splitEquiv_sigmaFactors σ)
    Y k

private theorem splitEquiv_twistedString_fst (Y : ∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion)
    (k : ℕ) :
    (splitEquiv (SectionFunctions.twistedString (sigmaFactors σ) Y k)).1 =
      SectionFunctions.twistedString (permTwist (realPerm σ) (aReal σ)) (splitEquiv Y).1 k := by
  rw [splitEquiv_twistedString]
  exact SectionFunctions.map_twistedString (MonoidHom.fst _ _)
    ((permTwist (realPerm σ) (aReal σ)).prodMap (permTwist (complexPerm σ) (aComplex σ)))
    (permTwist (realPerm σ) (aReal σ)) (fun _ => rfl) (splitEquiv Y) k

private theorem splitEquiv_twistedString_snd (Y : ∀ w : NumberField.InfinitePlace L, GL (Fin 2) w.Completion)
    (k : ℕ) :
    (splitEquiv (SectionFunctions.twistedString (sigmaFactors σ) Y k)).2 =
      SectionFunctions.twistedString (permTwist (complexPerm σ) (aComplex σ)) (splitEquiv Y).2 k := by
  rw [splitEquiv_twistedString]
  exact SectionFunctions.map_twistedString (MonoidHom.snd _ _)
    ((permTwist (realPerm σ) (aReal σ)).prodMap (permTwist (complexPerm σ) (aComplex σ)))
    (permTwist (complexPerm σ) (aComplex σ)) (fun _ => rfl) (splitEquiv Y) k

end SplitStrings

end SigmaCycleDescent

namespace SigmaCycleDescent

section Assembly

private theorem isTwistedProper_sigmaGL
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K))
    (hδ : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (NumberField.InfiniteAdeleRing K) σ δ))
    (hR : ∀ δ' : GL (Fin 2) ℝ, AutomorphicForm.IsRegularSemisimple δ' → IsTwistedProper (MonoidHom.id _) δ')
    (hC : ∀ δ' : GL (Fin 2) ℂ, AutomorphicForm.IsRegularSemisimple δ' → IsTwistedProper (MonoidHom.id _) δ')
    (hconj : ∀ δ' : GL (Fin 2) ℂ,
      AutomorphicForm.IsRegularSemisimple (δ' * Matrix.GeneralLinearGroup.map (starRingEnd ℂ) δ') →
      IsTwistedProper (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) δ') :
    IsTwistedProper (AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ) δ := by
  apply isTwistedProper_sigmaGL_of_sigmaFactors
  have hσ : σ ^ Module.finrank K L = 1 := TwistedOrbitProperness.pow_finrank_eq_one K L σ
  have hregF : ∀ w, AutomorphicForm.IsRegularSemisimple (SectionFunctions.twistedString (sigmaFactors σ)
      (TwistedOrbitProperness.archFactors K L δ) (Module.finrank K L) w) := by
    intro w
    rw [← archFactors_normString]
    exact isRegularSemisimple_archFactors hδ w
  have hsc : Function.Semiconj ⇑(TwistedOrbitProperness.archFactors K L)
      ⇑(AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ) ⇑(sigmaFactors σ) :=
    archFactors_sigmaGL σ
  have hperF : ∀ z, (⇑(sigmaFactors σ))^[Module.finrank K L] z = z := by
    intro z
    have h := hsc.iterate_right (Module.finrank K L) ((TwistedOrbitProperness.archFactors K L).symm z)
    rw [TwistedOrbitProperness.sigmaGL_iterate_finrank, ContinuousMulEquiv.apply_symm_apply] at h
    exact h.symm
  have hsplit : Function.Semiconj ⇑(splitEquiv (L := L)) ⇑(sigmaFactors σ)
      ⇑((permTwist (realPerm σ) (aReal σ)).prodMap (permTwist (complexPerm σ) (aComplex σ))) :=
    splitEquiv_sigmaFactors σ
  have hreal : IsTwistedProper (permTwist (realPerm σ) (aReal σ))
      (splitEquiv (TwistedOrbitProperness.archFactors K L δ)).1 := by
    have hfs : Function.Semiconj Prod.fst
        ⇑((permTwist (realPerm σ) (aReal σ)).prodMap (permTwist (complexPerm σ) (aComplex σ)))
        ⇑(permTwist (realPerm σ) (aReal σ)) :=
      fun _ => by rw [MonoidHom.coe_prodMap, Prod.map_fst]
    refine isTwistedProper_permTwist_of_forall_glMap (realPerm σ) (aReal σ)
      (fun r => ⟨(rhoReal σ r).toRingHom, continuous_rhoReal σ r,
        fun g => SectionFunctions.glContinuousMulEquiv_apply _ _ _ g⟩)
      _ (Module.finrank K L) (realPerm_iterate_eq_self σ hσ) ?_ ?_
      (fun ρ _ c _ δ' hreg' => isTwistedProper_glMap_real ρ c δ' hreg' hR)
    · intro r
      rw [← splitEquiv_twistedString_fst σ (TwistedOrbitProperness.archFactors K L δ) (Module.finrank K L),
        splitEquiv_apply_fst]
      exact SectionFunctions.isRegularSemisimple_glMap _ (hregF r.1)
    · intro Y
      have h1 := hsplit.iterate_right (Module.finrank K L) ((splitEquiv (L := L)).symm (Y, 1))
      rw [hperF, ContinuousMulEquiv.apply_symm_apply] at h1
      have h2 := hfs.iterate_right (Module.finrank K L) (Y, 1)
      rw [← h1] at h2
      exact h2.symm
  have hcomplex : IsTwistedProper (permTwist (complexPerm σ) (aComplex σ))
      (splitEquiv (TwistedOrbitProperness.archFactors K L δ)).2 := by
    have hss : Function.Semiconj Prod.snd
        ⇑((permTwist (realPerm σ) (aReal σ)).prodMap (permTwist (complexPerm σ) (aComplex σ)))
        ⇑(permTwist (complexPerm σ) (aComplex σ)) :=
      fun _ => by rw [MonoidHom.coe_prodMap, Prod.map_snd]
    refine isTwistedProper_permTwist_of_forall_glMap (complexPerm σ) (aComplex σ)
      (fun c => ⟨(rhoComplex σ c).toRingHom, continuous_rhoComplex σ c,
        fun g => SectionFunctions.glContinuousMulEquiv_apply _ _ _ g⟩)
      _ (Module.finrank K L) (complexPerm_iterate_eq_self σ hσ) ?_ ?_
      (fun ρ hρ c hρc δ' hreg' => isTwistedProper_glMap_complex ρ hρ c hρc δ' hreg' hC hconj)
    · intro c
      rw [← splitEquiv_twistedString_snd σ (TwistedOrbitProperness.archFactors K L δ) (Module.finrank K L),
        splitEquiv_apply_snd]
      exact SectionFunctions.isRegularSemisimple_glMap _ (hregF c.1)
    · intro Y
      have h1 := hsplit.iterate_right (Module.finrank K L) ((splitEquiv (L := L)).symm (1, Y))
      rw [hperF, ContinuousMulEquiv.apply_symm_apply] at h1
      have h2 := hss.iterate_right (Module.finrank K L) (1, Y)
      rw [← h1] at h2
      exact h2.symm
  have hmain : IsTwistedProper
      ((permTwist (realPerm σ) (aReal σ)).prodMap (permTwist (complexPerm σ) (aComplex σ)))
      (splitEquiv (TwistedOrbitProperness.archFactors K L δ)) :=
    isTwistedProper_prodMap _ _ hreal hcomplex
  have h2 := isTwistedProper_of_continuousMulEquiv (splitEquiv (L := L)).symm _ (sigmaFactors σ)
    (fun q => by
      apply (splitEquiv (L := L)).injective
      rw [splitEquiv_sigmaFactors, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply])
    _ hmain
  simpa using h2

end Assembly

end SigmaCycleDescent

namespace TwistedOrbitProperness

open AutomorphicForm

section Ring

variable {A : Type*} [CommRing A]

private theorem exists_eq_smul_one_add_smul_of_mul_eq_mul {G X : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X) :
    ∃ l m : A, X = l • (1 : Matrix (Fin 2) (Fin 2) A) + m • G := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hd
  obtain ⟨u, hu⟩ := hd
  have hu1 : (↑u⁻¹ : A) * ↑u = 1 := u.inv_mul
  have h00 : (X * G) 0 0 = (G * X) 0 0 := by rw [hX]
  have h01 : (X * G) 0 1 = (G * X) 0 1 := by rw [hX]
  have h10 : (X * G) 1 0 = (G * X) 1 0 := by rw [hX]
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  obtain ⟨Z, hZ⟩ : ∃ Z : A,
      Z = (G 0 0 - G 1 1) * (X 0 0 - X 1 1) + 2 * (G 1 0 * X 0 1 + G 0 1 * X 1 0) := ⟨_, rfl⟩
  refine ⟨X 0 0 - (↑u⁻¹ : A) * Z * G 0 0, (↑u⁻¹ : A) * Z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
    linear_combination (-(X 0 1)) * hu1 + (X 0 1 * (↑u⁻¹ : A)) * hu -
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h00 -
      ((↑u⁻¹ : A) * G 0 1) * hZ
  · simp
    linear_combination (-(X 1 0)) * hu1 + (X 1 0 * (↑u⁻¹ : A)) * hu +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h10 - (2 * (↑u⁻¹ : A) * G 1 0) * h00 -
      ((↑u⁻¹ : A) * G 1 0) * hZ
  · simp
    linear_combination (X 0 0 - X 1 1) * hu1 - ((X 0 0 - X 1 1) * (↑u⁻¹ : A)) * hu -
      (2 * (↑u⁻¹ : A) * G 1 0) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h10 +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * hZ

private theorem commute_of_mul_eq_mul_of_mul_eq_mul {G X Y : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X)
    (hY : Y * G = G * Y) :
    Commute X Y := by
  obtain ⟨l, m, rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hX
  obtain ⟨l', m', rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hY
  have c1 : Commute (1 : Matrix (Fin 2) (Fin 2) A) (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_left _).smul_right l').add_right ((Commute.one_left G).smul_right m')
  have c2 : Commute G (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_right G).smul_right l').add_right ((Commute.refl G).smul_right m')
  exact (c1.smul_left l).add_left (c2.smul_left m)

private theorem commute_of_mem_centralizer_of_isRegularSemisimple {g : GL (Fin 2) A}
    (hg : IsRegularSemisimple g) {x y : GL (Fin 2) A}
    (hx : x ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)))
    (hy : y ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) : Commute x y := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx hy
  have hx' : (x : Matrix (Fin 2) (Fin 2) A) * g = g * x := congrArg Units.val hx
  have hy' : (y : Matrix (Fin 2) (Fin 2) A) * g = g * y := congrArg Units.val hy
  exact Units.ext (commute_of_mul_eq_mul_of_mul_eq_mul hg hx' hy').eq

private theorem isMulCommutative_centralizer_of_isRegularSemisimple {g : GL (Fin 2) A}
    (hg : IsRegularSemisimple g) :
    IsMulCommutative (Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) :=
  ⟨⟨fun x y => Subtype.ext (commute_of_mem_centralizer_of_isRegularSemisimple hg x.2 y.2).eq⟩⟩

end Ring

section SigmaContinuous

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

omit [IsTopologicalRing A] in
private theorem continuous_sigmaTensor : Continuous (sigmaTensor K L A σ) := by
  have hs : ∀ (a : A) (x : L) (b : A), a • (x ⊗ₜ[K] b : L ⊗[K] A) = x ⊗ₜ (a * b) := by
    intro a x b
    simp only [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul]
    rw [TensorProduct.smul_tmul']
    simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]
  let f : L ⊗[K] A →ₗ[A] L ⊗[K] A :=
    { toFun := sigmaTensor K L A σ
      map_add' := fun x y => map_add (sigmaTensor K L A σ) x y
      map_smul' := fun a z => by
        rw [RingHom.id_apply]
        induction z with
        | zero => rw [smul_zero, map_zero, smul_zero]
        | tmul x b => rw [hs, sigmaTensor_tmul K L A σ, sigmaTensor_tmul K L A σ, hs]
        | add y w hy hw => rw [smul_add, map_add, map_add, smul_add, hy, hw] }
  exact IsModuleTopology.continuous_of_linearMap f

omit [IsTopologicalRing A] in
private theorem continuous_sigmaGL : Continuous (sigmaGL K L A σ) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_val.matrix_map (continuous_sigmaTensor K L A σ),
    Units.continuous_coe_inv.matrix_map (continuous_sigmaTensor K L A σ)⟩

end SigmaContinuous

section TwistedClosed

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  (σ : L ≃ₐ[K] L)

private theorem isClosed_twistedCentralizer_of_continuous (hσc : Continuous (sigmaGL K L A σ))
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensorGL K L A
  have h : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) = {t | t * δ * (sigmaGL K L A σ t)⁻¹ = δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [h]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul hσc.inv) continuous_const

end TwistedClosed

section CosetInvariance

variable (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)
  (δ : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K))

private theorem twistedOrbitMap_mul_left
    (t : AutomorphicForm.twistedCentralizer K L (NumberField.InfiniteAdeleRing K) σ δ)
    (x : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K)) :
    ((t : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K)) * x)⁻¹ * δ *
        AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ
          ((t : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K)) * x) =
      x⁻¹ * δ * AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ x := by
  have ht : (t : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K)) * δ *
      (AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ t)⁻¹ = δ :=
    AutomorphicForm.mem_sigmaCentralizer_iff.mp t.2
  have ht' : (t : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K)) * δ =
      δ * AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ t := mul_inv_eq_iff_eq_mul.mp ht
  have key : (t : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K))⁻¹ * δ *
      AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ t = δ := by
    rw [mul_assoc, ← ht', inv_mul_cancel_left]
  rw [map_mul, mul_inv_rev, ← mul_assoc, mul_assoc x⁻¹ _ δ, mul_assoc x⁻¹ (_ * δ), key]

end CosetInvariance

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
  (δ : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K))

private theorem isClosed_twistedCentralizer :
    IsClosed (AutomorphicForm.twistedCentralizer K L (NumberField.InfiniteAdeleRing K) σ δ :
      Set (GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K))) :=
  isClosed_twistedCentralizer_of_continuous K L (NumberField.InfiniteAdeleRing K) σ
    (continuous_sigmaGL K L (NumberField.InfiniteAdeleRing K) σ) δ

private theorem continuous_twistedOrbitMap :
    Continuous (fun x : GL (Fin 2) (L ⊗[K] NumberField.InfiniteAdeleRing K) =>
      x⁻¹ * δ * AutomorphicForm.sigmaGL K L (NumberField.InfiniteAdeleRing K) σ x) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (NumberField.InfiniteAdeleRing K)
  exact (continuous_inv.mul continuous_const).mul (continuous_sigmaGL K L (NumberField.InfiniteAdeleRing K) σ)

private theorem forall_commute_twistedCentralizer
    (hδ : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (NumberField.InfiniteAdeleRing K) σ δ))
    (a b : AutomorphicForm.twistedCentralizer K L (NumberField.InfiniteAdeleRing K) σ δ) :
    a * b = b * a :=
  Subtype.ext (commute_of_mem_centralizer_of_isRegularSemisimple hδ
    (twistedCentralizer_le_centralizer_normString K L (NumberField.InfiniteAdeleRing K) σ δ a.2)
    (twistedCentralizer_le_centralizer_normString K L (NumberField.InfiniteAdeleRing K) σ δ b.2)).eq

end SemiLocal

section CompanionCharts

open scoped Pointwise

variable {F : Type*} [NormedField F]

private def companion (t d : F) : Matrix (Fin 2) (Fin 2) F := !![0, -d; 1, t]

private def chartA (h : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F := !![1, h 0 0; 0, h 1 0]

private def chartB (h : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F := !![0, h 0 1; 1, h 1 1]

private def chartC (h : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  !![1, h 0 0 + h 0 1; 1, h 1 0 + h 1 1]

private theorem mul_chartA (h : Matrix (Fin 2) (Fin 2) F) :
    h * chartA h = chartA h * companion h.trace h.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartA, companion, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.det_fin_two] <;> ring

private theorem mul_chartB (h : Matrix (Fin 2) (Fin 2) F) :
    h * chartB h = chartB h * companion h.trace h.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartB, companion, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.det_fin_two] <;> ring

private theorem mul_chartC (h : Matrix (Fin 2) (Fin 2) F) :
    h * chartC h = chartC h * companion h.trace h.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartC, companion, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.det_fin_two] <;> ring

private theorem det_chartA (h : Matrix (Fin 2) (Fin 2) F) : (chartA h).det = h 1 0 := by
  simp [chartA, Matrix.det_fin_two]

private theorem det_chartB (h : Matrix (Fin 2) (Fin 2) F) : (chartB h).det = -h 0 1 := by
  simp [chartB, Matrix.det_fin_two]

private theorem det_chartC (h : Matrix (Fin 2) (Fin 2) F) :
    (chartC h).det = h 1 0 + h 1 1 - h 0 0 - h 0 1 := by
  simp [chartC, Matrix.det_fin_two]; ring

private theorem det_chart_ne_zero (h : Matrix (Fin 2) (Fin 2) F) (hd : h.trace ^ 2 - 4 * h.det ≠ 0) :
    (chartA h).det ≠ 0 ∨ (chartB h).det ≠ 0 ∨ (chartC h).det ≠ 0 := by
  by_contra habc
  simp only [not_or, not_not, det_chartA, det_chartB, det_chartC, neg_eq_zero] at habc
  obtain ⟨h10, h01, hC⟩ := habc
  apply hd
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, h10, h01]
  have h11 : h 1 1 = h 0 0 := by linear_combination hC - h10 + h01
  rw [h11]
  ring

private theorem continuous_chartA : Continuous (chartA : Matrix (Fin 2) (Fin 2) F → _) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [chartA] <;>
    first
      | exact continuous_const
      | exact continuous_id.matrix_elem _ _

private theorem continuous_chartB : Continuous (chartB : Matrix (Fin 2) (Fin 2) F → _) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [chartB] <;>
    first
      | exact continuous_const
      | exact continuous_id.matrix_elem _ _

private theorem continuous_chartC : Continuous (chartC : Matrix (Fin 2) (Fin 2) F → _) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [chartC] <;>
    first
      | exact continuous_const
      | exact (continuous_id.matrix_elem _ _).add (continuous_id.matrix_elem _ _)

private theorem inv_mul_mul_eq_of_mul_eq {P M N : Matrix (Fin 2) (Fin 2) F} (hP : IsUnit P.det)
    (h : M * P = P * N) : P⁻¹ * M * P = N := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]

private theorem val_mkOfDetNeZero {n : Type*} [DecidableEq n] [Fintype n] (A : Matrix n n F)
    (h : A.det ≠ 0) : ((Matrix.GeneralLinearGroup.mkOfDetNeZero A h : GL n F) : Matrix n n F) = A :=
  rfl

private theorem isCompact_range_chart {S : Set (GL (Fin 2) F)} (hS : IsCompact S)
    (chart : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F) (hchart : Continuous chart)
    (hne : ∀ h ∈ S, (chart (h : Matrix (Fin 2) (Fin 2) F)).det ≠ 0) (P₀ : GL (Fin 2) F) :
    IsCompact (Set.range fun h : S =>
      P₀ * (Matrix.GeneralLinearGroup.mkOfDetNeZero (chart (h : GL (Fin 2) F)) (hne h h.2))⁻¹) := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hc : Continuous fun h : S => chart ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
    hchart.comp (Units.continuous_val.comp continuous_subtype_val)
  have hu : Continuous fun h : S =>
      Matrix.GeneralLinearGroup.mkOfDetNeZero (chart (h : GL (Fin 2) F)) (hne h h.2) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact hc
    · simp only [Matrix.coe_units_inv, val_mkOfDetNeZero, Matrix.inv_def, Ring.inverse_eq_inv']
      exact (hc.matrix_det.inv₀ fun h => hne h h.2).smul hc.matrix_adjugate
  exact isCompact_range (continuous_const.mul hu.inv)

attribute [local irreducible] companion chartA chartB chartC in

private theorem isTwistedProper_id_of_chart (g P₀ : GL (Fin 2) F)
    (hd : (g : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 * (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0)
    (hP₀ : (g : Matrix (Fin 2) (Fin 2) F) * P₀ =
      P₀ * companion (g : Matrix (Fin 2) (Fin 2) F).trace (g : Matrix (Fin 2) (Fin 2) F).det) :
    SigmaCycleDescent.IsTwistedProper (MonoidHom.id _) g := by
  intro C hC

  let S : Set (GL (Fin 2) F) := C ∩
    {h | (h : Matrix (Fin 2) (Fin 2) F).trace = (g : Matrix (Fin 2) (Fin 2) F).trace} ∩
    {h | (h : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det}
  have hval : Continuous fun h : GL (Fin 2) F => (h : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have hS : IsCompact S :=
    (hC.inter_right (isClosed_eq hval.matrix_trace continuous_const)).inter_right
      (isClosed_eq hval.matrix_det continuous_const)

  let nA : GL (Fin 2) F → ℝ := fun h => ‖(chartA (h : Matrix (Fin 2) (Fin 2) F)).det‖
  let nB : GL (Fin 2) F → ℝ := fun h => ‖(chartB (h : Matrix (Fin 2) (Fin 2) F)).det‖
  let nC : GL (Fin 2) F → ℝ := fun h => ‖(chartC (h : Matrix (Fin 2) (Fin 2) F)).det‖
  have hnA : Continuous nA := continuous_norm.comp (continuous_chartA.comp hval).matrix_det
  have hnB : Continuous nB := continuous_norm.comp (continuous_chartB.comp hval).matrix_det
  have hnC : Continuous nC := continuous_norm.comp (continuous_chartC.comp hval).matrix_det
  let SA : Set (GL (Fin 2) F) := S ∩ {h | nB h ≤ nA h} ∩ {h | nC h ≤ nA h}
  let SB : Set (GL (Fin 2) F) := S ∩ {h | nA h ≤ nB h} ∩ {h | nC h ≤ nB h}
  let SC : Set (GL (Fin 2) F) := S ∩ {h | nA h ≤ nC h} ∩ {h | nB h ≤ nC h}
  have hSA : IsCompact SA := (hS.inter_right (isClosed_le hnB hnA)).inter_right (isClosed_le hnC hnA)
  have hSB : IsCompact SB := (hS.inter_right (isClosed_le hnA hnB)).inter_right (isClosed_le hnC hnB)
  have hSC : IsCompact SC := (hS.inter_right (isClosed_le hnA hnC)).inter_right (isClosed_le hnB hnC)

  have hdS : ∀ h ∈ S, (h : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 * (h : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rintro h ⟨⟨-, htr⟩, hdet⟩
    rw [Set.mem_setOf_eq] at htr hdet
    rw [htr, hdet]
    exact hd
  have hneA : ∀ h ∈ SA, (chartA (h : Matrix (Fin 2) (Fin 2) F)).det ≠ 0 := by
    rintro h ⟨⟨hS', hBA⟩, hCA⟩ h0
    have h0' : nA h = 0 := by simp [nA, h0]
    rw [Set.mem_setOf_eq, h0'] at hBA hCA
    rcases det_chart_ne_zero _ (hdS h hS') with hA' | hB' | hC'
    · exact hA' h0
    · exact hB' (norm_le_zero_iff.mp hBA)
    · exact hC' (norm_le_zero_iff.mp hCA)
  have hneB : ∀ h ∈ SB, (chartB (h : Matrix (Fin 2) (Fin 2) F)).det ≠ 0 := by
    rintro h ⟨⟨hS', hAB⟩, hCB⟩ h0
    have h0' : nB h = 0 := by simp [nB, h0]
    rw [Set.mem_setOf_eq, h0'] at hAB hCB
    rcases det_chart_ne_zero _ (hdS h hS') with hA' | hB' | hC'
    · exact hA' (norm_le_zero_iff.mp hAB)
    · exact hB' h0
    · exact hC' (norm_le_zero_iff.mp hCB)
  have hneC : ∀ h ∈ SC, (chartC (h : Matrix (Fin 2) (Fin 2) F)).det ≠ 0 := by
    rintro h ⟨⟨hS', hAC⟩, hBC⟩ h0
    have h0' : nC h = 0 := by simp [nC, h0]
    rw [Set.mem_setOf_eq, h0'] at hAC hBC
    rcases det_chart_ne_zero _ (hdS h hS') with hA' | hB' | hC'
    · exact hA' (norm_le_zero_iff.mp hAC)
    · exact hB' (norm_le_zero_iff.mp hBC)
    · exact hC' h0

  let fA : SA → GL (Fin 2) F := fun h =>
    P₀ * (Matrix.GeneralLinearGroup.mkOfDetNeZero (chartA (h : GL (Fin 2) F)) (hneA h h.2))⁻¹
  let fB : SB → GL (Fin 2) F := fun h =>
    P₀ * (Matrix.GeneralLinearGroup.mkOfDetNeZero (chartB (h : GL (Fin 2) F)) (hneB h h.2))⁻¹
  let fC : SC → GL (Fin 2) F := fun h =>
    P₀ * (Matrix.GeneralLinearGroup.mkOfDetNeZero (chartC (h : GL (Fin 2) F)) (hneC h h.2))⁻¹
  refine ⟨Set.range fA ∪ Set.range fB ∪ Set.range fC,
    ((isCompact_range_chart hSA chartA continuous_chartA hneA P₀).union
      (isCompact_range_chart hSB chartB continuous_chartB hneB P₀)).union
      (isCompact_range_chart hSC chartC continuous_chartC hneC P₀), ?_⟩

  intro x hx
  simp only [Set.mem_preimage, MonoidHom.id_apply] at hx
  have hval_h : ((x⁻¹ * g * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (↑x⁻¹ : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) *
        (x : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Units.val_mul]
  have htr : ((x⁻¹ * g * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace =
      (g : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [hval_h]; exact Matrix.trace_units_conj' x _
  have hdet : ((x⁻¹ * g * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (g : Matrix (Fin 2) (Fin 2) F).det := by
    rw [hval_h]; exact Matrix.det_units_conj' x _
  have hS' : x⁻¹ * g * x ∈ S := ⟨⟨hx, htr⟩, hdet⟩

  have hC₀ : ((P₀⁻¹ * g * P₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      companion (g : Matrix (Fin 2) (Fin 2) F).trace (g : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact inv_mul_mul_eq_of_mul_eq (Matrix.isUnits_det_units P₀) hP₀

  have rel : ∀ (chart : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F),
      (∀ h : Matrix (Fin 2) (Fin 2) F, h * chart h = chart h * companion h.trace h.det) →
      ∀ (h P : GL (Fin 2) F), (P : Matrix (Fin 2) (Fin 2) F) = chart h →
      (h : Matrix (Fin 2) (Fin 2) F).trace = (g : Matrix (Fin 2) (Fin 2) F).trace →
      (h : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det →
      h * P = P * (P₀⁻¹ * g * P₀) := by
    intro chart hchart h P hP htr' hdet'
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hC₀, hP, hchart, htr', hdet']

  have key : ∀ P : GL (Fin 2) F, x⁻¹ * g * x * P = P * (P₀⁻¹ * g * P₀) →
      x * P * P₀⁻¹ ∈ (AutomorphicForm.sigmaCentralizer (MonoidHom.id _) g : Set (GL (Fin 2) F)) := by
    intro P hP
    rw [SetLike.mem_coe, AutomorphicForm.mem_sigmaCentralizer_iff, MonoidHom.id_apply]
    calc x * P * P₀⁻¹ * g * (x * P * P₀⁻¹)⁻¹
        = x * (P * (P₀⁻¹ * g * P₀)) * P⁻¹ * x⁻¹ := by group
      _ = x * (x⁻¹ * g * x * P) * P⁻¹ * x⁻¹ := by rw [hP]
      _ = g := by group
  have cover : ∀ P : GL (Fin 2) F, x⁻¹ * g * x * P = P * (P₀⁻¹ * g * P₀) →
      P₀ * P⁻¹ ∈ Set.range fA ∪ Set.range fB ∪ Set.range fC →
      x ∈ (AutomorphicForm.sigmaCentralizer (MonoidHom.id _) g : Set (GL (Fin 2) F)) *
        (Set.range fA ∪ Set.range fB ∪ Set.range fC) := by
    intro P hP hD
    exact Set.mem_mul.mpr ⟨x * P * P₀⁻¹, key P hP, P₀ * P⁻¹, hD, by group⟩

  rcases le_total (nB (x⁻¹ * g * x)) (nA (x⁻¹ * g * x)) with hBA | hAB
  · rcases le_total (nC (x⁻¹ * g * x)) (nA (x⁻¹ * g * x)) with hCA | hAC
    · have hmem : x⁻¹ * g * x ∈ SA := ⟨⟨hS', hBA⟩, hCA⟩
      exact cover _ (rel chartA mul_chartA (x⁻¹ * g * x)
        (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hneA _ hmem)) (val_mkOfDetNeZero _ _) htr hdet)
        (Set.mem_union_left _ (Set.mem_union_left _ ⟨⟨x⁻¹ * g * x, hmem⟩, rfl⟩))
    · have hmem : x⁻¹ * g * x ∈ SC := ⟨⟨hS', hAC⟩, hBA.trans hAC⟩
      exact cover _ (rel chartC mul_chartC (x⁻¹ * g * x)
        (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hneC _ hmem)) (val_mkOfDetNeZero _ _) htr hdet)
        (Set.mem_union_right _ ⟨⟨x⁻¹ * g * x, hmem⟩, rfl⟩)
  · rcases le_total (nC (x⁻¹ * g * x)) (nB (x⁻¹ * g * x)) with hCB | hBC
    · have hmem : x⁻¹ * g * x ∈ SB := ⟨⟨hS', hAB⟩, hCB⟩
      exact cover _ (rel chartB mul_chartB (x⁻¹ * g * x)
        (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hneB _ hmem)) (val_mkOfDetNeZero _ _) htr hdet)
        (Set.mem_union_left _ (Set.mem_union_right _ ⟨⟨x⁻¹ * g * x, hmem⟩, rfl⟩))
    · have hmem : x⁻¹ * g * x ∈ SC := ⟨⟨hS', hAB.trans hBC⟩, hBC⟩
      exact cover _ (rel chartC mul_chartC (x⁻¹ * g * x)
        (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hneC _ hmem)) (val_mkOfDetNeZero _ _) htr hdet)
        (Set.mem_union_right _ ⟨⟨x⁻¹ * g * x, hmem⟩, rfl⟩)

private theorem isTwistedProper_id_of_isRegularSemisimple (g : GL (Fin 2) F)
    (hg : AutomorphicForm.IsRegularSemisimple g) :
    SigmaCycleDescent.IsTwistedProper (MonoidHom.id _) g := by
  have hd := (AutomorphicForm.isRegularSemisimple_iff_ne_zero g).mp hg
  rcases det_chart_ne_zero (g : Matrix (Fin 2) (Fin 2) F) hd with hA | hB | hC
  · exact isTwistedProper_id_of_chart g (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA) hd
      (by rw [val_mkOfDetNeZero]; exact mul_chartA _)
  · exact isTwistedProper_id_of_chart g (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hB) hd
      (by rw [val_mkOfDetNeZero]; exact mul_chartB _)
  · exact isTwistedProper_id_of_chart g (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hC) hd
      (by rw [val_mkOfDetNeZero]; exact mul_chartC _)

end CompanionCharts

section OneFactor

private theorem isTwistedProper_id_real (δ' : GL (Fin 2) ℝ) (hδ' : AutomorphicForm.IsRegularSemisimple δ') :
    SigmaCycleDescent.IsTwistedProper (MonoidHom.id _) δ' :=
  isTwistedProper_id_of_isRegularSemisimple δ' hδ'

private theorem isTwistedProper_id_complex (δ' : GL (Fin 2) ℂ)
    (hδ' : AutomorphicForm.IsRegularSemisimple δ') :
    SigmaCycleDescent.IsTwistedProper (MonoidHom.id _) δ' :=
  isTwistedProper_id_of_isRegularSemisimple δ' hδ'

end OneFactor

section ConjTwist

open scoped Pointwise ComplexConjugate

local notation "conjGL" => Matrix.GeneralLinearGroup.map (n := Fin 2) (starRingEnd ℂ)

private theorem conjGL_conjGL (x : GL (Fin 2) ℂ) : conjGL (conjGL x) = x :=
  Units.ext (Matrix.ext fun i j => by simp [Matrix.GeneralLinearGroup.map_apply])

private theorem continuous_conjGL : Continuous (conjGL : GL (Fin 2) ℂ → GL (Fin 2) ℂ) :=
  Units.continuous_iff.mpr
    ⟨Units.continuous_val.matrix_map Complex.continuous_conj,
      Units.continuous_coe_inv.matrix_map Complex.continuous_conj⟩

private theorem isTwistedProper_of_twistedConj {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (θ : G →* G) (δ P : G)
    (h : SigmaCycleDescent.IsTwistedProper θ (P⁻¹ * δ * θ P)) :
    SigmaCycleDescent.IsTwistedProper θ δ := by
  intro C hC
  obtain ⟨D, hD, hsub⟩ := h C hC
  refine ⟨(fun d => P * d) '' D, hD.image (continuous_const.mul continuous_id), ?_⟩
  intro x hx
  have hx' : x⁻¹ * δ * θ x ∈ C := hx
  have hy : P⁻¹ * x ∈ (fun y => y⁻¹ * (P⁻¹ * δ * θ P) * θ y) ⁻¹' C := by
    show (P⁻¹ * x)⁻¹ * (P⁻¹ * δ * θ P) * θ (P⁻¹ * x) ∈ C
    rw [map_mul, map_inv]
    have e : (P⁻¹ * x)⁻¹ * (P⁻¹ * δ * θ P) * ((θ P)⁻¹ * θ x) = x⁻¹ * δ * θ x := by group
    rw [e]
    exact hx'
  obtain ⟨t, ht, d, hd, htd⟩ := Set.mem_mul.mp (hsub hy)
  refine Set.mem_mul.mpr ⟨P * t * P⁻¹, ?_, P * d, Set.mem_image_of_mem _ hd, ?_⟩
  · rw [SetLike.mem_coe, AutomorphicForm.mem_sigmaCentralizer_iff] at ht ⊢
    rw [map_mul, map_mul, map_inv]
    calc P * t * P⁻¹ * δ * (θ P * θ t * (θ P)⁻¹)⁻¹
        = P * (t * (P⁻¹ * δ * θ P) * (θ t)⁻¹) * (θ P)⁻¹ := by group
      _ = P * (P⁻¹ * δ * θ P) * (θ P)⁻¹ := by rw [ht]
      _ = δ := by group
  · calc P * t * P⁻¹ * (P * d) = P * (t * d) := by group
      _ = P * (P⁻¹ * x) := by rw [htd]
      _ = x := by group

private theorem isTwistedProper_of_norm {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (θ : G →* G) (hθ : Continuous θ) (hθ2 : ∀ x, θ (θ x) = x) (δ : G)
    (hN : SigmaCycleDescent.IsTwistedProper (MonoidHom.id G) (δ * θ δ))
    (hL : ∀ C₄ : Set G, IsCompact C₄ → ∃ D₁ : Set G, IsCompact D₁ ∧
      ∀ z ∈ AutomorphicForm.sigmaCentralizer (MonoidHom.id G) (δ * θ δ),
        z⁻¹ * δ * θ z ∈ C₄ → z ∈ (AutomorphicForm.sigmaCentralizer θ δ : Set G) * D₁) :
    SigmaCycleDescent.IsTwistedProper θ δ := by
  intro C hC
  obtain ⟨D₀, hD₀, hsub₀⟩ := hN ((fun c => c * θ c) '' C) (hC.image (continuous_id.mul hθ))
  obtain ⟨D₁, hD₁, hL₁⟩ := hL ((fun p : G × G => p.1 * p.2 * (θ p.1)⁻¹) '' (D₀ ×ˢ C))
    ((hD₀.prod hC).image ((continuous_fst.mul continuous_snd).mul (hθ.comp continuous_fst).inv))
  refine ⟨D₁ * D₀, hD₁.mul hD₀, ?_⟩
  intro x hx
  have hx' : x⁻¹ * δ * θ x ∈ C := hx
  have hx₂ : x ∈ (fun y => y⁻¹ * (δ * θ δ) * (MonoidHom.id G) y) ⁻¹' ((fun c => c * θ c) '' C) := by
    refine ⟨x⁻¹ * δ * θ x, hx', ?_⟩
    show x⁻¹ * δ * θ x * θ (x⁻¹ * δ * θ x) = x⁻¹ * (δ * θ δ) * (MonoidHom.id G) x
    rw [MonoidHom.id_apply, map_mul, map_mul, map_inv, hθ2]
    group
  obtain ⟨z, hz, d₀, hd₀, rfl⟩ := Set.mem_mul.mp (hsub₀ hx₂)
  have hz₄ : z⁻¹ * δ * θ z ∈ (fun p : G × G => p.1 * p.2 * (θ p.1)⁻¹) '' (D₀ ×ˢ C) := by
    refine ⟨(d₀, (z * d₀)⁻¹ * δ * θ (z * d₀)), ⟨hd₀, hx'⟩, ?_⟩
    show d₀ * ((z * d₀)⁻¹ * δ * θ (z * d₀)) * (θ d₀)⁻¹ = z⁻¹ * δ * θ z
    rw [map_mul]
    group
  obtain ⟨t, ht, d₁, hd₁, htd⟩ := Set.mem_mul.mp (hL₁ z hz hz₄)
  exact Set.mem_mul.mpr ⟨t, ht, d₁ * d₀, Set.mul_mem_mul hd₁ hd₀, by rw [← mul_assoc, htd]⟩

private theorem exists_conj_eq_diagonal (N : GL (Fin 2) ℂ) (hN : AutomorphicForm.IsRegularSemisimple N) :
    ∃ (Q : GL (Fin 2) ℂ) (l₁ l₂ : ℂ), l₁ ≠ l₂ ∧
      ((Q⁻¹ * N * Q : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![l₁, 0; 0, l₂] := by
  have hd := (AutomorphicForm.isRegularSemisimple_iff_ne_zero N).mp hN
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self
    ((N : Matrix (Fin 2) (Fin 2) ℂ).trace ^ 2 - 4 * (N : Matrix (Fin 2) (Fin 2) ℂ).det)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hd (by rw [hs, mul_zero])

  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : GL (Fin 2) ℂ, (N : Matrix (Fin 2) (Fin 2) ℂ) * P₀ =
      P₀ * companion (N : Matrix (Fin 2) (Fin 2) ℂ).trace (N : Matrix (Fin 2) (Fin 2) ℂ).det := by
    rcases det_chart_ne_zero (N : Matrix (Fin 2) (Fin 2) ℂ) hd with hA | hB | hC
    · exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA, by rw [val_mkOfDetNeZero]; exact mul_chartA _⟩
    · exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hB, by rw [val_mkOfDetNeZero]; exact mul_chartB _⟩
    · exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hC, by rw [val_mkOfDetNeZero]; exact mul_chartC _⟩

  set t := (N : Matrix (Fin 2) (Fin 2) ℂ).trace with ht
  set d := (N : Matrix (Fin 2) (Fin 2) ℂ).det with hdd
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ℂ, r₁ = (t + s) / 2 := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r₂ : ℂ, r₂ = (t - s) / 2 := ⟨_, rfl⟩
  have hr : r₁ - r₂ = s := by rw [hr₁, hr₂]; ring
  have hsum : r₁ + r₂ = t := by rw [hr₁, hr₂]; ring
  have hprod : r₁ * r₂ = d := by rw [hr₁, hr₂]; linear_combination (1 / 4 : ℂ) * hs
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin 2) ℂ, (P : Matrix (Fin 2) (Fin 2) ℂ) = !![-r₂, -r₁; 1, 1] := by
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ ?_, val_mkOfDetNeZero _ _⟩
    rw [Matrix.det_fin_two_of]
    intro h0
    apply hs0
    rw [← hr]
    linear_combination h0
  have hCP : companion t d * !![-r₂, -r₁; 1, 1] = !![-r₂, -r₁; 1, 1] * !![r₁, 0; 0, r₂] := by
    rw [← hsum, ← hprod]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [companion, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring
  refine ⟨P₀ * P, r₁, r₂, fun h => hs0 (by rw [← hr, h, sub_self]), ?_⟩
  have hNQ : (N : Matrix (Fin 2) (Fin 2) ℂ) * ((P₀ * P : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((P₀ * P : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * !![r₁, 0; 0, r₂] := by
    rw [Units.val_mul, ← Matrix.mul_assoc, hP₀, Matrix.mul_assoc, hP, hCP, Matrix.mul_assoc]
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact inv_mul_mul_eq_of_mul_eq (Matrix.isUnits_det_units _) hNQ

private theorem apply_eq_zero_of_mem_sigmaCentralizer (ΛGL : GL (Fin 2) ℂ) (l₁ l₂ : ℂ) (hl : l₁ ≠ l₂)
    (hΛ : (ΛGL : Matrix (Fin 2) (Fin 2) ℂ) = !![l₁, 0; 0, l₂]) {z : GL (Fin 2) ℂ}
    (hz : z ∈ AutomorphicForm.sigmaCentralizer (MonoidHom.id _) ΛGL) :
    (z : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (z : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
  have hc : z * ΛGL = ΛGL * z := by
    have h := AutomorphicForm.mem_sigmaCentralizer_iff.mp hz
    rw [MonoidHom.id_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hm := congrArg (fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ)) hc
  simp only [Units.val_mul, hΛ] at hm
  have e01 : (z : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * l₂ = l₁ * (z : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 0) 1
  have e10 : (z : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * l₁ = l₂ * (z : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 1) 0
  constructor
  · by_contra h
    exact hl (mul_left_cancel₀ h (e01.trans (mul_comm _ _))).symm
  · by_contra h
    exact hl (mul_left_cancel₀ h (e10.trans (mul_comm _ _)))

private theorem shape_of_mul_conjGL_eq (δ ΛGL : GL (Fin 2) ℂ) (l₁ l₂ : ℂ) (hl : l₁ ≠ l₂)
    (hΛ : (ΛGL : Matrix (Fin 2) (Fin 2) ℂ) = !![l₁, 0; 0, l₂]) (hN : δ * conjGL δ = ΛGL) :
    ((δ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) ∨
      ((δ : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0) := by
  have hN2 : conjGL δ * δ = conjGL ΛGL := by rw [← hN, map_mul, conjGL_conjGL]
  have hc : ΛGL * δ = δ * conjGL ΛGL := by rw [← hN2, ← mul_assoc, hN]
  have hm := congrArg (fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ)) hc
  simp only [Units.val_mul, hΛ] at hm
  set M := (δ : Matrix (Fin 2) (Fin 2) ℂ) with hM
  have e00 : l₁ * M 0 0 = M 0 0 * conj l₁ := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply, hΛ] using
      congrFun (congrFun hm 0) 0
  have e01 : l₁ * M 0 1 = M 0 1 * conj l₂ := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply, hΛ] using
      congrFun (congrFun hm 0) 1
  have e10 : l₂ * M 1 0 = M 1 0 * conj l₁ := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply, hΛ] using
      congrFun (congrFun hm 1) 0
  have e11 : l₂ * M 1 1 = M 1 1 * conj l₂ := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply, hΛ] using
      congrFun (congrFun hm 1) 1
  have hdet : M.det ≠ 0 := (Matrix.isUnits_det_units δ).ne_zero

  have k00 : M 0 0 ≠ 0 → l₁ = conj l₁ := fun h => mul_right_cancel₀ h (e00.trans (mul_comm _ _))
  have k01 : M 0 1 ≠ 0 → l₁ = conj l₂ := fun h => mul_right_cancel₀ h (e01.trans (mul_comm _ _))
  have k10 : M 1 0 ≠ 0 → l₂ = conj l₁ := fun h => mul_right_cancel₀ h (e10.trans (mul_comm _ _))
  have k11 : M 1 1 ≠ 0 → l₂ = conj l₂ := fun h => mul_right_cancel₀ h (e11.trans (mul_comm _ _))
  by_cases h01 : M 0 1 = 0
  · by_cases h10 : M 1 0 = 0
    · exact Or.inl ⟨h01, h10⟩
    ·
      exfalso
      have h00 : M 0 0 ≠ 0 := by
        rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
        exact left_ne_zero_of_mul hdet
      exact hl (by rw [k10 h10, ← k00 h00])
  · right
    constructor
    ·
      by_contra h00
      apply hl
      have h := (k00 h00).symm.trans (k01 h01)
      simpa using congrArg conj h
    ·
      by_contra h11
      exact hl (by rw [k01 h01, ← k11 h11])

private theorem isCompact_range_mkOfDetNeZero {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → Matrix (Fin 2) (Fin 2) ℂ) (hf : Continuous f) (hne : ∀ x, (f x).det ≠ 0) :
    IsCompact (Set.range fun x => Matrix.GeneralLinearGroup.mkOfDetNeZero (f x) (hne x)) := by
  refine isCompact_range (Units.continuous_iff.mpr ⟨hf, ?_⟩)
  simp only [Matrix.coe_units_inv, val_mkOfDetNeZero, Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hf.matrix_det.inv₀ hne).smul hf.matrix_adjugate

private theorem lang_of_diagonal (δ ΛGL : GL (Fin 2) ℂ) (l₁ l₂ : ℂ) (hl : l₁ ≠ l₂)
    (hΛ : (ΛGL : Matrix (Fin 2) (Fin 2) ℂ) = !![l₁, 0; 0, l₂])
    (h01 : (δ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0) (h10 : (δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) :
    ∃ D₁ : Set (GL (Fin 2) ℂ), IsCompact D₁ ∧
      ∀ z ∈ AutomorphicForm.sigmaCentralizer (MonoidHom.id _) ΛGL,
        z ∈ (AutomorphicForm.sigmaCentralizer conjGL δ : Set (GL (Fin 2) ℂ)) * D₁ := by

  let S : Set (ℂ × ℂ) := Metric.sphere (0 : ℂ) 1 ×ˢ Metric.sphere (0 : ℂ) 1
  have hS : IsCompact S := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let f : S → Matrix (Fin 2) (Fin 2) ℂ := fun p => !![(p : ℂ × ℂ).1, 0; 0, (p : ℂ × ℂ).2]
  have hf : Continuous f := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [f] <;>
      first
        | exact continuous_const
        | exact continuous_fst.comp continuous_subtype_val
        | exact continuous_snd.comp continuous_subtype_val
  have hmem : ∀ p : S, ‖(p : ℂ × ℂ).1‖ = 1 ∧ ‖(p : ℂ × ℂ).2‖ = 1 := fun p =>
    ⟨mem_sphere_zero_iff_norm.mp p.2.1, mem_sphere_zero_iff_norm.mp p.2.2⟩
  have hne : ∀ p : S, (f p).det ≠ 0 := by
    intro p
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero]
    exact mul_ne_zero (norm_ne_zero_iff.mp (by rw [(hmem p).1]; exact one_ne_zero))
      (norm_ne_zero_iff.mp (by rw [(hmem p).2]; exact one_ne_zero))
  refine ⟨_, isCompact_range_mkOfDetNeZero f hf hne, ?_⟩
  intro z hz
  obtain ⟨hz01, hz10⟩ := apply_eq_zero_of_mem_sigmaCentralizer ΛGL l₁ l₂ hl hΛ hz
  have huv : (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (z : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
    have h := (Matrix.isUnits_det_units z).ne_zero
    rwa [Matrix.det_fin_two, hz01, zero_mul, sub_zero] at h
  have hu0 : (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ 0 := left_ne_zero_of_mul huv
  have hv0 : (z : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := right_ne_zero_of_mul huv
  have hnu : (‖(z : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu0)
  have hnv : (‖(z : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv0)

  obtain ⟨t, ht⟩ : ∃ t : GL (Fin 2) ℂ, (t : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(‖(z : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ : ℂ), 0; 0, (‖(z : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ : ℂ)] := by
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ ?_, val_mkOfDetNeZero _ _⟩
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero]
    exact mul_ne_zero hnu hnv

  have hp : ((z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 / ‖(z : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖,
      (z : Matrix (Fin 2) (Fin 2) ℂ) 1 1 / ‖(z : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖) ∈ S := by
    constructor
    · rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self]
      exact norm_ne_zero_iff.mpr hu0
    · rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self]
      exact norm_ne_zero_iff.mpr hv0
  have hfp : f ⟨_, hp⟩ =
      !![(z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 / ‖(z : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖, 0;
        0, (z : Matrix (Fin 2) (Fin 2) ℂ) 1 1 / ‖(z : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖] := rfl
  refine Set.mem_mul.mpr ⟨t, ?_, Matrix.GeneralLinearGroup.mkOfDetNeZero (f ⟨_, hp⟩) (hne ⟨_, hp⟩),
    ⟨⟨_, hp⟩, rfl⟩, ?_⟩
  ·
    rw [SetLike.mem_coe, AutomorphicForm.mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [Units.val_mul, Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ht, h01, h10, Complex.conj_ofReal, mul_comm]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [Units.val_mul, ht, val_mkOfDetNeZero, hfp]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hz01, hz10]
    all_goals first
      | rw [← mul_div_assoc, mul_div_cancel_left₀ _ hnu]
      | rw [← mul_div_assoc, mul_div_cancel_left₀ _ hnv]

private theorem lang_of_antidiagonal (δ ΛGL : GL (Fin 2) ℂ) (l₁ l₂ : ℂ) (hl : l₁ ≠ l₂)
    (hΛ : (ΛGL : Matrix (Fin 2) (Fin 2) ℂ) = !![l₁, 0; 0, l₂])
    (h00 : (δ : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0) (h11 : (δ : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0)
    (C₄ : Set (GL (Fin 2) ℂ)) (hC₄ : IsCompact C₄) :
    ∃ D₁ : Set (GL (Fin 2) ℂ), IsCompact D₁ ∧
      ∀ z ∈ AutomorphicForm.sigmaCentralizer (MonoidHom.id _) ΛGL, z⁻¹ * δ * conjGL z ∈ C₄ →
        z ∈ (AutomorphicForm.sigmaCentralizer conjGL δ : Set (GL (Fin 2) ℂ)) * D₁ := by
  have hab : (δ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 := by
    have h := (Matrix.isUnits_det_units δ).ne_zero
    rwa [Matrix.det_fin_two, h00, zero_mul, zero_sub, neg_ne_zero] at h
  have ha0 : (δ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 ≠ 0 := left_ne_zero_of_mul hab
  have hb0 : (δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 := right_ne_zero_of_mul hab
  have hbc : conj ((δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hb0

  have hval : Continuous fun c : GL (Fin 2) ℂ => (c : Matrix (Fin 2) (Fin 2) ℂ) := Units.continuous_val
  let E : Set (ℂ × ℂ) :=
    (fun c : GL (Fin 2) ℂ => ((c : Matrix (Fin 2) (Fin 2) ℂ) 0 1, (c : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) '' C₄
  let S : Set (ℂ × ℂ) :=
    E ∩ {p | p.1 * conj p.2 = (δ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * conj ((δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0)}
  have hS : IsCompact S :=
    (hC₄.image ((hval.matrix_elem 0 1).prodMk (hval.matrix_elem 1 0))).inter_right
      (isClosed_eq (continuous_fst.mul (Complex.continuous_conj.comp continuous_snd)) continuous_const)
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hne2 : ∀ p : S, conj (p : ℂ × ℂ).2 ≠ 0 := by
    intro p h
    apply mul_ne_zero ha0 hbc
    rw [← p.2.2, h, mul_zero]
  let f : S → Matrix (Fin 2) (Fin 2) ℂ := fun p =>
    !![conj (p : ℂ × ℂ).2 / conj ((δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0), 0; 0, 1]
  have hf : Continuous f := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [f] <;>
      first
        | exact continuous_const
        | exact ((Complex.continuous_conj.comp (continuous_snd.comp continuous_subtype_val)).div_const _)
  have hne : ∀ p : S, (f p).det ≠ 0 := by
    intro p
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero, mul_one]
    exact div_ne_zero (hne2 p) hbc
  refine ⟨_, isCompact_range_mkOfDetNeZero f hf hne, ?_⟩
  intro z hz hzC
  obtain ⟨hz01, hz10⟩ := apply_eq_zero_of_mem_sigmaCentralizer ΛGL l₁ l₂ hl hΛ hz
  have huv : (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (z : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
    have h := (Matrix.isUnits_det_units z).ne_zero
    rwa [Matrix.det_fin_two, hz01, zero_mul, sub_zero] at h
  have hu0 : (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ 0 := left_ne_zero_of_mul huv
  have hv0 : (z : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := right_ne_zero_of_mul huv
  have hvc : conj ((z : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hv0

  obtain ⟨c, hc⟩ : ∃ c : GL (Fin 2) ℂ, z⁻¹ * δ * conjGL z = c := ⟨_, rfl⟩
  rw [hc] at hzC
  have hzc : δ * conjGL z = z * c := by rw [← hc]; group
  have hm := congrArg (fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ)) hzc
  simp only [Units.val_mul] at hm
  have e01 : (δ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * conj ((z : Matrix (Fin 2) (Fin 2) ℂ) 1 1) =
      (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (c : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply, h00, h11, hz01,
      hz10] using congrFun (congrFun hm 0) 1
  have e10 : (δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * conj ((z : Matrix (Fin 2) (Fin 2) ℂ) 0 0) =
      (z : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * (c : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply, h00, h11, hz01,
      hz10] using congrFun (congrFun hm 1) 0
  have e10' : conj ((z : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * conj ((c : Matrix (Fin 2) (Fin 2) ℂ) 1 0) =
      conj ((δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
    have h := congrArg conj e10
    simp only [map_mul, starRingEnd_self_apply] at h
    exact h.symm

  have hp : (((c : Matrix (Fin 2) (Fin 2) ℂ) 0 1, (c : Matrix (Fin 2) (Fin 2) ℂ) 1 0) : ℂ × ℂ) ∈ S := by
    refine ⟨⟨c, hzC, rfl⟩, ?_⟩
    show (c : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * conj ((c : Matrix (Fin 2) (Fin 2) ℂ) 1 0) =
      (δ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * conj ((δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
    have key : (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * conj ((z : Matrix (Fin 2) (Fin 2) ℂ) 1 1) *
        ((c : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * conj ((c : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) =
        (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * conj ((z : Matrix (Fin 2) (Fin 2) ℂ) 1 1) *
          ((δ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * conj ((δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) := by
      calc (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * conj ((z : Matrix (Fin 2) (Fin 2) ℂ) 1 1) *
            ((c : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * conj ((c : Matrix (Fin 2) (Fin 2) ℂ) 1 0))
          = (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (c : Matrix (Fin 2) (Fin 2) ℂ) 0 1 *
              (conj ((z : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * conj ((c : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) := by
            ring
        _ = (δ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * conj ((z : Matrix (Fin 2) (Fin 2) ℂ) 1 1) *
              (conj ((δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by rw [← e01, e10']
        _ = (z : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * conj ((z : Matrix (Fin 2) (Fin 2) ℂ) 1 1) *
              ((δ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * conj ((δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) := by ring
    exact mul_left_cancel₀ (mul_ne_zero hu0 hvc) key

  obtain ⟨t, ht⟩ : ∃ t : GL (Fin 2) ℂ,
      (t : Matrix (Fin 2) (Fin 2) ℂ) =
        !![conj ((z : Matrix (Fin 2) (Fin 2) ℂ) 1 1), 0; 0, (z : Matrix (Fin 2) (Fin 2) ℂ) 1 1] := by
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ ?_, val_mkOfDetNeZero _ _⟩
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero]
    exact mul_ne_zero hvc hv0
  have hfp : f ⟨_, hp⟩ =
      !![conj ((c : Matrix (Fin 2) (Fin 2) ℂ) 1 0) / conj ((δ : Matrix (Fin 2) (Fin 2) ℂ) 1 0), 0; 0, 1] := rfl
  refine Set.mem_mul.mpr ⟨t, ?_, Matrix.GeneralLinearGroup.mkOfDetNeZero (f ⟨_, hp⟩) (hne ⟨_, hp⟩),
    ⟨⟨_, hp⟩, rfl⟩, ?_⟩
  · rw [SetLike.mem_coe, AutomorphicForm.mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [Units.val_mul, Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ht, h00, h11, mul_comm]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [Units.val_mul, ht, val_mkOfDetNeZero, hfp]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hz01, hz10]
    all_goals rw [← mul_div_assoc, e10', mul_div_cancel_left₀ _ hbc]

private theorem isTwistedProper_conj (δ' : GL (Fin 2) ℂ)
    (hδ' : AutomorphicForm.IsRegularSemisimple (δ' * Matrix.GeneralLinearGroup.map (starRingEnd ℂ) δ')) :
    SigmaCycleDescent.IsTwistedProper (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) δ' := by
  obtain ⟨Q, l₁, l₂, hl, hΛ⟩ := exists_conj_eq_diagonal _ hδ'
  refine isTwistedProper_of_twistedConj conjGL δ' Q ?_
  set δ := Q⁻¹ * δ' * conjGL Q with hδ
  set ΛGL := Q⁻¹ * (δ' * conjGL δ') * Q with hΛGL
  have hN : δ * conjGL δ = ΛGL := by
    rw [hδ, hΛGL, map_mul, map_mul, map_inv, conjGL_conjGL]
    group
  refine isTwistedProper_of_norm conjGL continuous_conjGL conjGL_conjGL δ ?_ ?_
  ·
    rw [hN]
    refine isTwistedProper_id_of_isRegularSemisimple _ ?_
    rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero, hΛ, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
    intro h
    apply hl
    have h2 : (l₁ - l₂) ^ 2 = 0 := by linear_combination h
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  · intro C₄ hC₄
    rcases shape_of_mul_conjGL_eq δ ΛGL l₁ l₂ hl hΛ hN with ⟨h01, h10⟩ | ⟨h00, h11⟩
    · obtain ⟨D₁, hD₁, hmem⟩ := lang_of_diagonal δ ΛGL l₁ l₂ hl hΛ h01 h10
      exact ⟨D₁, hD₁, fun z hz _ => hmem z (by rwa [hN] at hz)⟩
    · obtain ⟨D₁, hD₁, hmem⟩ := lang_of_antidiagonal δ ΛGL l₁ l₂ hl hΛ h00 h11 C₄ hC₄
      exact ⟨D₁, hD₁, fun z hz hzC => hmem z (by rwa [hN] at hz) hzC⟩

end ConjTwist

end TwistedOrbitProperness

open NumberField MeasureTheory

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ']
    (φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ w : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ,
      AutomorphicForm.IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ δ τ' φ w ∧ Continuous w := by
  letI hmG : MeasurableSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensorGL K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)
  letI hmT : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) :=
    AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := ⟨rfl⟩
  haveI := TwistedOrbitProperness.secondCountableTopology_infiniteAdeleRing K
  haveI := TwistedOrbitProperness.secondCountableTopology_tensor K L (InfiniteAdeleRing K)
  haveI : SecondCountableTopology (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    TwistedOrbitProperness.secondCountableTopology_gl (L ⊗[K] InfiniteAdeleRing K)
  haveI : τ'.IsMulRightInvariant :=
    SectionFunctions.isMulRightInvariant_of_forall_commute
      (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) τ'
      (TwistedOrbitProperness.forall_commute_twistedCentralizer K L σ δ hδ)
  obtain ⟨w, h0, hm, hc, h1, hw⟩ :=
    SectionFunctions.exists_continuous_section
      (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) τ'
      (TwistedOrbitProperness.isClosed_twistedCentralizer K L σ δ)
      (TwistedOrbitProperness.continuous_twistedOrbitMap K L σ δ)
      (TwistedOrbitProperness.twistedOrbitMap_mul_left K L σ δ)
      (fun C hC => SigmaCycleDescent.isTwistedProper_sigmaGL K L σ δ hδ
        TwistedOrbitProperness.isTwistedProper_id_real TwistedOrbitProperness.isTwistedProper_id_complex
        TwistedOrbitProperness.isTwistedProper_conj C hC)
      hφ
  refine ⟨w, ?_, hw⟩
  unfold AutomorphicForm.IsTwistedSectionFnOn
  exact ⟨h0, hm, hc, fun x hx => h1 x (subset_tsupport φ hx)⟩

end S_AutomorphicForm_exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport (solution)
