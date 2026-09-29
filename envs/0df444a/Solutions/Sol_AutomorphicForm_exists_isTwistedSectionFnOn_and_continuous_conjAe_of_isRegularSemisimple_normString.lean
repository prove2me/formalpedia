-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_conjAe_of_isRegularSemisimple_normString
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/33879784-bf3a-50ce-944b-4646587887ca

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_conjAe_of_isRegularSemisimple_normString

set_option autoImplicit false

open scoped TensorProduct

namespace TSModel

noncomputable def ridC : ℂ ⊗[ℝ] ℝ ≃+* ℂ := (Algebra.TensorProduct.rid ℝ ℝ ℂ).toRingEquiv

theorem ridC_tmul (z : ℂ) (a : ℝ) : ridC (z ⊗ₜ a) = a • z := rfl

end TSModel

open scoped TensorProduct.RightActions

namespace TMSectionFunctions

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

end TMSectionFunctions

namespace TMSectionFunctions

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

end TMSectionFunctions

namespace TMTwistedOrbitProperness

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

end Countability

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

end TMTwistedOrbitProperness

namespace TMSigmaCycleDescent

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

end TMSigmaCycleDescent

namespace TMTwistedOrbitProperness

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
    TMSigmaCycleDescent.IsTwistedProper (MonoidHom.id _) g := by
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
    TMSigmaCycleDescent.IsTwistedProper (MonoidHom.id _) g := by
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
    TMSigmaCycleDescent.IsTwistedProper (MonoidHom.id _) δ' :=
  isTwistedProper_id_of_isRegularSemisimple δ' hδ'

private theorem isTwistedProper_id_complex (δ' : GL (Fin 2) ℂ)
    (hδ' : AutomorphicForm.IsRegularSemisimple δ') :
    TMSigmaCycleDescent.IsTwistedProper (MonoidHom.id _) δ' :=
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
    (h : TMSigmaCycleDescent.IsTwistedProper θ (P⁻¹ * δ * θ P)) :
    TMSigmaCycleDescent.IsTwistedProper θ δ := by
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
    (hN : TMSigmaCycleDescent.IsTwistedProper (MonoidHom.id G) (δ * θ δ))
    (hL : ∀ C₄ : Set G, IsCompact C₄ → ∃ D₁ : Set G, IsCompact D₁ ∧
      ∀ z ∈ AutomorphicForm.sigmaCentralizer (MonoidHom.id G) (δ * θ δ),
        z⁻¹ * δ * θ z ∈ C₄ → z ∈ (AutomorphicForm.sigmaCentralizer θ δ : Set G) * D₁) :
    TMSigmaCycleDescent.IsTwistedProper θ δ := by
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
    TMSigmaCycleDescent.IsTwistedProper (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) δ' := by
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

end TMTwistedOrbitProperness

namespace TSModel

open AutomorphicForm MeasureTheory
open TMSigmaCycleDescent
open scoped Pointwise ComplexConjugate

section TensorMaps

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_ringHom_tensor {B : Type} [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : L ⊗[K] A →+* B) (hφ : Continuous fun a : A => φ ((1 : L) ⊗ₜ[K] a)) : Continuous φ := by
  haveI := isTopologicalRing_tensor K L A
  refine IsModuleTopology.continuous_of_ringHom (R := A) φ ?_
  have h : ⇑(φ.comp (algebraMap A (L ⊗[K] A))) = fun a : A => φ ((1 : L) ⊗ₜ[K] a) := by
    funext a
    rfl
  rw [h]
  exact hφ

theorem continuous_symm_tensor [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
    {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [T2Space B] [LocallyCompactSpace B]
    (e : L ⊗[K] A ≃+* B) (he : Continuous e) : Continuous e.symm := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensor K L A
  haveI := locallyCompactSpace_tensor K L A
  haveI := TMTwistedOrbitProperness.secondCountableTopology_tensor K L A
  have hopen : IsOpenMap e := e.toAddMonoidHom.isOpenMap_of_sigmaCompact e.surjective he
  exact (e.toEquiv.toHomeomorphOfContinuousOpen he hopen).symm.continuous

end TensorMaps

section Model

theorem continuous_ridC : Continuous ridC := by
  refine continuous_ringHom_tensor ℝ ℂ ℝ ridC.toRingHom ?_
  have h : (fun a : ℝ => ridC.toRingHom ((1 : ℂ) ⊗ₜ[ℝ] a)) = fun a : ℝ => a • (1 : ℂ) := by
    funext a
    exact ridC_tmul 1 a
  rw [h]
  exact continuous_id.smul continuous_const

theorem continuous_ridC_symm : Continuous ridC.symm :=
  continuous_symm_tensor ℝ ℂ ℝ ridC continuous_ridC

theorem ridC_sigmaTensor (z : ℂ ⊗[ℝ] ℝ) :
    ridC (sigmaTensor ℝ ℂ ℝ Complex.conjAe z) = conj (ridC z) := by
  induction z with
  | zero => simp
  | tmul x a =>
    rw [TMTwistedOrbitProperness.sigmaTensor_tmul, ridC_tmul, ridC_tmul]
    rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

local notation "conjGL" => Matrix.GeneralLinearGroup.map (n := Fin 2) (starRingEnd ℂ)

noncomputable def E : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) ≃ₜ* GL (Fin 2) ℂ :=
  TMSectionFunctions.glContinuousMulEquiv ridC continuous_ridC continuous_ridC_symm

theorem E_apply (g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : E g = Matrix.GeneralLinearGroup.map ridC.toRingHom g :=
  TMSectionFunctions.glContinuousMulEquiv_apply _ _ _ g

theorem E_sigmaGL (g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    E (sigmaGL ℝ ℂ ℝ Complex.conjAe g) = conjGL (E g) := by
  rw [E_apply, E_apply]
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp only [sigmaGL, Matrix.GeneralLinearGroup.map_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact ridC_sigmaTensor _

theorem E_symm_conjGL (h : GL (Fin 2) ℂ) :
    E.symm (conjGL h) = sigmaGL ℝ ℂ ℝ Complex.conjAe (E.symm h) := by
  apply E.injective
  rw [E_sigmaGL, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]

theorem normString_eq (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    normString ℝ ℂ ℝ Complex.conjAe δ = δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ := by
  show ((List.range (Module.finrank ℝ ℂ)).map fun i => (⇑(sigmaGL ℝ ℂ ℝ Complex.conjAe))^[i] δ).prod = _
  rw [Complex.finrank_real_complex]
  simp [List.range_succ]

theorem isTwistedProper_model (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ)) :
    IsTwistedProper (sigmaGL ℝ ℂ ℝ Complex.conjAe) δ := by
  have hE : IsRegularSemisimple (E δ * conjGL (E δ)) := by
    rw [← E_sigmaGL, ← map_mul, ← normString_eq, E_apply]
    exact TMSectionFunctions.isRegularSemisimple_glMap _ hδ
  have hC := TMTwistedOrbitProperness.isTwistedProper_conj (E δ) hE
  have h := isTwistedProper_of_continuousMulEquiv E.symm
    (Matrix.GeneralLinearGroup.map (n := Fin 2) (starRingEnd ℂ)) (sigmaGL ℝ ℂ ℝ Complex.conjAe)
    E_symm_conjGL (E δ) hC
  rwa [ContinuousMulEquiv.symm_apply_apply] at h

end Model

end TSModel

open MeasureTheory AutomorphicForm in

theorem solution
    (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ))
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ,
      IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ' φ W ∧ Continuous W := by
  letI hmG : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := t2Space_tensorGL ℝ ℂ ℝ
  haveI := locallyCompactSpace_tensorGL ℝ ℂ ℝ
  letI hmT : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :=
    twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := ⟨rfl⟩
  haveI := TMTwistedOrbitProperness.secondCountableTopology_tensor ℝ ℂ ℝ
  haveI : SecondCountableTopology (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    TMTwistedOrbitProperness.secondCountableTopology_gl (ℂ ⊗[ℝ] ℝ)
  haveI : τ'.IsHaarMeasure := hτ'
  haveI : τ'.IsMulRightInvariant :=
    TMSectionFunctions.isMulRightInvariant_of_forall_commute (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) τ'
      (fun a b => Subtype.ext (TMTwistedOrbitProperness.commute_of_mem_centralizer_of_isRegularSemisimple hδ
        (TMTwistedOrbitProperness.twistedCentralizer_le_centralizer_normString ℝ ℂ ℝ Complex.conjAe δ a.2)
        (TMTwistedOrbitProperness.twistedCentralizer_le_centralizer_normString ℝ ℂ ℝ Complex.conjAe δ b.2)).eq)
  have hcl := TMTwistedOrbitProperness.isClosed_twistedCentralizer_of_continuous ℝ ℂ ℝ Complex.conjAe
    (TMTwistedOrbitProperness.continuous_sigmaGL ℝ ℂ ℝ Complex.conjAe) δ
  have hinv : ∀ (t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)),
      ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * x)⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * x) =
        x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x := by
    intro t x
    have ht : (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * δ * (sigmaGL ℝ ℂ ℝ Complex.conjAe t)⁻¹ = δ :=
      AutomorphicForm.mem_sigmaCentralizer_iff.mp t.2
    have ht' : (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * δ = δ * sigmaGL ℝ ℂ ℝ Complex.conjAe t := mul_inv_eq_iff_eq_mul.mp ht
    have key : (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe t = δ := by
      rw [mul_assoc, ← ht', inv_mul_cancel_left]
    rw [map_mul, mul_inv_rev, ← mul_assoc, mul_assoc x⁻¹ _ δ, mul_assoc x⁻¹ (_ * δ), key]
  obtain ⟨w, h0, hm, hc, h1, hw⟩ :=
    TMSectionFunctions.exists_continuous_section (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) τ' hcl
      ((continuous_inv.mul continuous_const).mul (TMTwistedOrbitProperness.continuous_sigmaGL ℝ ℂ ℝ Complex.conjAe))
      hinv (fun C hC => TSModel.isTwistedProper_model δ hδ C hC) hφ
  refine ⟨w, ?_, hw⟩
  unfold IsTwistedSectionFnOn
  exact ⟨h0, hm, hc, fun x hx => h1 x (subset_tsupport φ hx)⟩

end S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_conjAe_of_isRegularSemisimple_normString
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_conjAe_of_isRegularSemisimple_normString (solution)
