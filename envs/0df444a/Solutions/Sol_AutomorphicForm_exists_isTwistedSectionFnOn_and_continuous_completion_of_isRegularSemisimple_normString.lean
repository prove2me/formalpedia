-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/398f8115-4f24-56cb-8f28-876ec0d23267

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul
import Theorems.Thm_AutomorphicForm_exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString

set_option autoImplicit false

open scoped TensorProduct TensorProduct.RightActions

namespace TSRSectionFunctions

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

end TSRSectionFunctions

namespace TSRSectionFunctions

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

end TSRSectionFunctions

namespace TSRTwistedOrbitProperness

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

end TSRTwistedOrbitProperness

namespace TSRSigmaCycleDescent

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

end TSRSigmaCycleDescent

namespace TSRTwistedOrbitProperness

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

end TSRTwistedOrbitProperness

namespace TSReg

open AutomorphicForm MeasureTheory NumberField
open TSRSigmaCycleDescent
open scoped Pointwise

section Factor

variable {ι : Type*} {H : ι → Type*} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]

theorem isTwistedProper_of_piTwist [DecidableEq ι] (θ : ∀ i, H i →* H i) (δ : ∀ i, H i)
    (h : IsTwistedProper (piTwist θ) δ) (i : ι) : IsTwistedProper (θ i) (δ i) := by
  rw [isTwistedProper_iff] at h ⊢
  intro C hC
  have hC' : IsCompact ((fun c : H i => Function.update δ i c) '' C) :=
    hC.image (continuous_const.update i continuous_id)
  obtain ⟨D, hD, hfac⟩ := h _ hC'
  refine ⟨(fun y : ∀ j, H j => y i) '' D, hD.image (continuous_apply i), fun x hx => ?_⟩
  have hX : (Function.update (1 : ∀ j, H j) i x)⁻¹ * δ * piTwist θ (Function.update (1 : ∀ j, H j) i x) ∈
      (fun c : H i => Function.update δ i c) '' C := by
    refine ⟨x⁻¹ * δ i * θ i x, hx, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp [piTwist_apply]
    · simp [piTwist_apply, Function.update_of_ne hj]
  obtain ⟨t, ht, d, hd, htd⟩ := hfac _ hX
  refine ⟨t i, ?_, d i, ⟨d, hd, rfl⟩, ?_⟩
  · rw [AutomorphicForm.mem_sigmaCentralizer_iff] at ht ⊢
    have hti := congrFun ht i
    simpa [piTwist_apply] using hti
  · have htdi := congrFun htd i
    simpa using htdi

end Factor

section FromSections

variable {G : Type*} [Group G] [TopologicalSpace G] [T2Space G]

theorem isTwistedProper_of_forall_exists_section (θ : G →* G) (δ : G)
    {mT : MeasurableSpace (sigmaCentralizer θ δ)} (τ : Measure (sigmaCentralizer θ δ))
    (h : ∀ φ : G → ℂ, HasCompactSupport φ → ∃ w : G → ℝ, HasCompactSupport w ∧
      ∀ x, φ (x⁻¹ * δ * θ x) ≠ 0 → ∫ t : sigmaCentralizer θ δ, w ((t : G) * x) ∂τ = 1) :
    IsTwistedProper θ δ := by
  classical
  intro C hC
  obtain ⟨w, hwc, hw⟩ := h (C.indicator fun _ => (1 : ℂ))
    (HasCompactSupport.intro hC (fun x hx => Set.indicator_of_notMem hx _))
  refine ⟨tsupport w, hwc, fun x hx => ?_⟩
  have hxC : x⁻¹ * δ * θ x ∈ C := hx
  have hx' : (C.indicator fun _ => (1 : ℂ)) (x⁻¹ * δ * θ x) ≠ 0 := by
    rw [Set.indicator_of_mem hxC]
    exact one_ne_zero
  have h1 := hw x hx'
  have hex : ∃ t : sigmaCentralizer θ δ, w ((t : G) * x) ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hz : (fun t : sigmaCentralizer θ δ => w ((t : G) * x)) = fun _ => 0 := funext hne
    rw [hz, integral_zero] at h1
    exact zero_ne_one h1
  obtain ⟨t, ht⟩ := hex
  refine ⟨((t⁻¹ : sigmaCentralizer θ δ) : G), (t⁻¹).2, (t : G) * x, subset_tsupport _ ht, ?_⟩
  show ((t⁻¹ : sigmaCentralizer θ δ) : G) * ((t : G) * x) = x
  rw [Subgroup.coe_inv, inv_mul_cancel_left]

end FromSections

section NormString

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem map_normString {A B : Type} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (σ : L ≃ₐ[K] L) (Φ : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B))
    (hΦ : ∀ g, Φ (sigmaGL K L A σ g) = sigmaGL K L B σ (Φ g)) (δ : GL (Fin 2) (L ⊗[K] A)) :
    Φ (normString K L A σ δ) = normString K L B σ (Φ δ) :=
  TSRSectionFunctions.map_twistedString Φ (sigmaGL K L A σ) (sigmaGL K L B σ) hΦ δ (Module.finrank K L)

theorem sigmaGL_toTensorGL {A : Type} [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (g : GL (Fin 2) A) :
    sigmaGL K L A σ (toTensorGL K L A g) = toTensorGL K L A g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show sigmaTensor K L A σ (Algebra.TensorProduct.includeRight (R := K) (A := L) ((g : Matrix (Fin 2) (Fin 2) A) i j)) =
    Algebra.TensorProduct.includeRight (R := K) (A := L) ((g : Matrix (Fin 2) (Fin 2) A) i j)
  rw [Algebra.TensorProduct.includeRight_apply, TSRTwistedOrbitProperness.sigmaTensor_tmul, map_one]

theorem normString_toTensorGL {A : Type} [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (g : GL (Fin 2) A) :
    normString K L A σ (toTensorGL K L A g) = toTensorGL K L A (g ^ Module.finrank K L) := by
  have h := TSRSectionFunctions.map_twistedString (toTensorGL K L A) (MonoidHom.id _) (sigmaGL K L A σ)
    (fun x => (sigmaGL_toTensorGL K L σ x).symm) g (Module.finrank K L)
  rw [TSRSectionFunctions.twistedString_of_forall_eq (f := MonoidHom.id _) (fun _ => rfl)] at h
  exact h.symm

theorem exists_isRegularSemisimple_pow (F : Type) [Field F] [CharZero F] (n : ℕ) (hn : n ≠ 0) :
    ∃ g : GL (Fin 2) F, IsRegularSemisimple (g ^ n) := by
  have hdet : Matrix.det (Matrix.diagonal ![(1 : F), 2]) ≠ 0 := by
    rw [Matrix.det_diagonal]
    simp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
  rw [isRegularSemisimple_iff_ne_zero]
  have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet ^ n : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal (![(1 : F), 2] ^ n) := by
    rw [Units.val_pow_eq_pow_val]
    show (Matrix.diagonal ![(1 : F), 2]) ^ n = _
    rw [Matrix.diagonal_pow]
  rw [hcoe, Matrix.det_diagonal, Matrix.trace_diagonal]
  simp only [Fin.sum_univ_two, Fin.prod_univ_two, Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_pow]
  have h2 : (2 : F) ^ n ≠ 1 := by
    intro h
    have h' : ((2 ^ n : ℕ) : F) = ((1 : ℕ) : F) := by push_cast; exact h
    have h'' := Nat.cast_injective h'
    rw [Nat.pow_eq_one] at h''
    rcases h'' with h2 | h0
    · norm_num at h2
    · exact hn h0
  have : (1 + (2 : F) ^ n) ^ 2 - 4 * (1 * (2 : F) ^ n) = ((2 : F) ^ n - 1) ^ 2 := by ring
  rw [this]
  exact pow_ne_zero 2 (sub_ne_zero.mpr h2)

theorem disc_map {R S : Type*} [CommRing R] [CommRing S] (e : R →+* S) (g : GL (Fin 2) R) :
    Matrix.trace ((Matrix.GeneralLinearGroup.map e g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) ^ 2 -
        4 * Matrix.det ((Matrix.GeneralLinearGroup.map e g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      e (Matrix.trace (g : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) R)) := by
  rw [TSRSectionFunctions.coe_glMap]
  have htr : Matrix.trace ((g : Matrix (Fin 2) (Fin 2) R).map e) = e (Matrix.trace (g : Matrix (Fin 2) (Fin 2) R)) := by
    simp [Matrix.trace]
  have hdet : Matrix.det ((g : Matrix (Fin 2) (Fin 2) R).map e) = e (Matrix.det (g : Matrix (Fin 2) (Fin 2) R)) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  rw [htr, hdet]
  simp [map_ofNat]

theorem isRegularSemisimple_of_pi {R : Type*} {ι : Type*} {S : ι → Type*} [CommRing R] [∀ i, CommRing (S i)]
    (Ξ : R ≃+* ((i : ι) → S i)) (g : GL (Fin 2) R)
    (h : ∀ i, IsRegularSemisimple (Matrix.GeneralLinearGroup.map ((Pi.evalRingHom S i).comp Ξ.toRingHom) g)) :
    IsRegularSemisimple g := by
  unfold IsRegularSemisimple at h ⊢
  have hΞ : IsUnit (Ξ (Matrix.trace (g : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) R))) := by
    rw [Pi.isUnit_iff]
    intro i
    have hi := h i
    rw [disc_map] at hi
    exact hi
  have h' := hΞ.map Ξ.symm
  rwa [RingEquiv.symm_apply_apply] at h'

end NormString

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : InfinitePlace K)

theorem isTwistedProper_infiniteAdeleRing
    (δA : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδA : IsRegularSemisimple (normString K L (InfiniteAdeleRing K) σ δA)) :
    IsTwistedProper (sigmaGL K L (InfiniteAdeleRing K) σ) δA := by
  classical
  haveI := isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := t2Space_tensorGL K L (InfiniteAdeleRing K)
  haveI := locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)
  letI hmT : MeasurableSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ δA) :=
    twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δA
  haveI : BorelSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ δA) := ⟨rfl⟩
  have hcl := TSRTwistedOrbitProperness.isClosed_twistedCentralizer_of_continuous K L (InfiniteAdeleRing K) σ
    (TSRTwistedOrbitProperness.continuous_sigmaGL K L (InfiniteAdeleRing K) σ) δA
  haveI : LocallyCompactSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ δA) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (twistedCentralizer K L (InfiniteAdeleRing K) σ δA)) :=
    inferInstance
  refine isTwistedProper_of_forall_exists_section (sigmaGL K L (InfiniteAdeleRing K) σ) δA
    (Measure.haarMeasure K₀) fun φ hφ => ?_
  obtain ⟨w, hw, -⟩ :=
    AutomorphicForm.exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
      K L σ δA hδA (Measure.haarMeasure K₀) φ hφ
  exact ⟨w, hw.2.2.1, hw.2.2.2⟩

theorem isTwistedProper_completion
    (δ : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : IsRegularSemisimple (normString K L v.Completion σ δ)) :
    IsTwistedProper (sigmaGL K L v.Completion σ) δ := by
  classical
  obtain ⟨Ξ, hΞ, hΞ', hΞt⟩ := AutomorphicForm.exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul K L
  obtain ⟨Θ, hΘ, hΘ', hΘc, hΘσ, -⟩ :=
    AutomorphicForm.exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi K L Ξ hΞ hΞ' hΞt

  have hn : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  have hfill : ∀ w : InfinitePlace K, ∃ d : GL (Fin 2) (L ⊗[K] w.Completion),
      IsRegularSemisimple (normString K L w.Completion σ d) := by
    intro w
    haveI : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap K w.Completion).injective
    obtain ⟨g, hg⟩ := exists_isRegularSemisimple_pow w.Completion (Module.finrank K L) hn
    refine ⟨toTensorGL K L w.Completion g, ?_⟩
    rw [normString_toTensorGL K L σ g]
    exact TSRSectionFunctions.isRegularSemisimple_glMap _ hg
  choose d₀ hd₀ using hfill

  obtain ⟨δA, hδA⟩ : ∃ δA : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), Θ δA = Function.update d₀ v δ :=
    ⟨Θ.symm (Function.update d₀ v δ), Θ.apply_symm_apply _⟩

  have hNw : ∀ w : InfinitePlace K,
      Θ (normString K L (InfiniteAdeleRing K) σ δA) w = normString K L w.Completion σ (Θ δA w) :=
    fun w => map_normString K L σ
      ((Pi.evalMonoidHom (fun w : InfinitePlace K => GL (Fin 2) (L ⊗[K] w.Completion)) w).comp Θ.toMonoidHom)
      (fun g => hΘσ σ g w) δA
  have hregA : IsRegularSemisimple (normString K L (InfiniteAdeleRing K) σ δA) := by
    refine isRegularSemisimple_of_pi Ξ _ fun w => ?_
    rw [← hΘc, hNw w, hδA]
    by_cases hvw : w = v
    · subst hvw
      rw [Function.update_self]
      exact hδ
    · rw [Function.update_of_ne hvw]
      exact hd₀ w

  have hA := isTwistedProper_infiniteAdeleRing K L σ δA hregA
  let Θc : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ*
      ((w : InfinitePlace K) → GL (Fin 2) (L ⊗[K] w.Completion)) :=
    { Θ with continuous_toFun := hΘ, continuous_invFun := hΘ' }
  have hPi : IsTwistedProper (piTwist fun w : InfinitePlace K => sigmaGL K L w.Completion σ) (Θ δA) :=
    isTwistedProper_of_continuousMulEquiv Θc (sigmaGL K L (InfiniteAdeleRing K) σ)
      (piTwist fun w : InfinitePlace K => sigmaGL K L w.Completion σ)
      (fun g => funext fun w => hΘσ σ g w) δA hA
  have hv := isTwistedProper_of_piTwist (fun w : InfinitePlace K => sigmaGL K L w.Completion σ) (Θ δA) hPi v
  rwa [hδA, Function.update_self] at hv

omit [NumberField K] [NumberField L] in

theorem twistedOrbitMap_mul_left {A : Type} [CommRing A] [Algebra K A]
    (δ : GL (Fin 2) (L ⊗[K] A)) (t : twistedCentralizer K L A σ δ) (x : GL (Fin 2) (L ⊗[K] A)) :
    ((t : GL (Fin 2) (L ⊗[K] A)) * x)⁻¹ * δ * sigmaGL K L A σ ((t : GL (Fin 2) (L ⊗[K] A)) * x) =
      x⁻¹ * δ * sigmaGL K L A σ x := by
  have ht : (t : GL (Fin 2) (L ⊗[K] A)) * δ * (sigmaGL K L A σ t)⁻¹ = δ :=
    AutomorphicForm.mem_sigmaCentralizer_iff.mp t.2
  have ht' : (t : GL (Fin 2) (L ⊗[K] A)) * δ = δ * sigmaGL K L A σ t := mul_inv_eq_iff_eq_mul.mp ht
  have key : (t : GL (Fin 2) (L ⊗[K] A))⁻¹ * δ * sigmaGL K L A σ t = δ := by
    rw [mul_assoc, ← ht', inv_mul_cancel_left]
  rw [map_mul, mul_inv_rev, ← mul_assoc, mul_assoc x⁻¹ _ δ, mul_assoc x⁻¹ (_ * δ), key]

end Main

end TSReg

open MeasureTheory NumberField AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K)
    (δ : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : IsRegularSemisimple (normString K L v.Completion σ δ))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (L ⊗[K] v.Completion) → ℝ,
      IsTwistedSectionFnOn K L v.Completion σ δ τ' φ W ∧ Continuous W := by
  letI hmG : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.Completion)) := glBorelOf (L ⊗[K] v.Completion)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.Completion)) := borelSpace_glBorelOf (L ⊗[K] v.Completion)
  haveI := isTopologicalGroup_tensorGL K L v.Completion
  haveI := t2Space_tensorGL K L v.Completion
  haveI := locallyCompactSpace_tensorGL K L v.Completion
  letI hmT : MeasurableSpace (twistedCentralizer K L v.Completion σ δ) :=
    twistedCentralizerBorel K L v.Completion σ δ
  haveI : BorelSpace (twistedCentralizer K L v.Completion σ δ) := ⟨rfl⟩
  haveI : SecondCountableTopology v.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  haveI := TSRTwistedOrbitProperness.secondCountableTopology_tensor K L v.Completion
  haveI : SecondCountableTopology (GL (Fin 2) (L ⊗[K] v.Completion)) :=
    TSRTwistedOrbitProperness.secondCountableTopology_gl (L ⊗[K] v.Completion)
  haveI : τ'.IsHaarMeasure := hτ'
  haveI : τ'.IsMulRightInvariant :=
    TSRSectionFunctions.isMulRightInvariant_of_forall_commute (twistedCentralizer K L v.Completion σ δ) τ'
      (fun a b => Subtype.ext (TSRTwistedOrbitProperness.commute_of_mem_centralizer_of_isRegularSemisimple hδ
        (TSRTwistedOrbitProperness.twistedCentralizer_le_centralizer_normString K L v.Completion σ δ a.2)
        (TSRTwistedOrbitProperness.twistedCentralizer_le_centralizer_normString K L v.Completion σ δ b.2)).eq)
  obtain ⟨w, h0, hm, hc, h1, hw⟩ :=
    TSRSectionFunctions.exists_continuous_section (twistedCentralizer K L v.Completion σ δ) τ'
      (TSRTwistedOrbitProperness.isClosed_twistedCentralizer_of_continuous K L v.Completion σ
        (TSRTwistedOrbitProperness.continuous_sigmaGL K L v.Completion σ) δ)
      ((continuous_inv.mul continuous_const).mul (TSRTwistedOrbitProperness.continuous_sigmaGL K L v.Completion σ))
      (TSReg.twistedOrbitMap_mul_left K L σ δ)
      (fun C hC => TSReg.isTwistedProper_completion K L σ v δ hδ C hC)
      hφ
  refine ⟨w, ?_, hw⟩
  unfold IsTwistedSectionFnOn
  exact ⟨h0, hm, hc, fun x hx => h1 x (subset_tsupport φ hx)⟩

end S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString (solution)
