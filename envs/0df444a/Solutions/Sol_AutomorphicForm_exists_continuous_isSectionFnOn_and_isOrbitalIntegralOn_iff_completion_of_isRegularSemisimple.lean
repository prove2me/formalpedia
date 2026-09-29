-- Prove2me | solution 1 for AutomorphicForm.exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3a973c74-541f-5c67-aa94-3c5fca5e8fa8

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_IsOrbitalIntegralOn_unique_of_isRegularSemisimple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple

set_option autoImplicit false

open scoped TensorProduct TensorProduct.RightActions

namespace S30ArchSectionFn

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

end S30ArchSectionFn

namespace S30OrbitProperness

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

end S30OrbitProperness

set_option autoImplicit false

namespace S30TwistProper

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

end S30TwistProper

namespace S30OrbitProperness

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
    S30TwistProper.IsTwistedProper (MonoidHom.id _) g := by
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
    S30TwistProper.IsTwistedProper (MonoidHom.id _) g := by
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
    S30TwistProper.IsTwistedProper (MonoidHom.id _) δ' :=
  isTwistedProper_id_of_isRegularSemisimple δ' hδ'

private theorem isTwistedProper_id_complex (δ' : GL (Fin 2) ℂ)
    (hδ' : AutomorphicForm.IsRegularSemisimple δ') :
    S30TwistProper.IsTwistedProper (MonoidHom.id _) δ' :=
  isTwistedProper_id_of_isRegularSemisimple δ' hδ'

end OneFactor

end S30OrbitProperness

namespace S30UntwistedSection

open AutomorphicForm

variable {F : Type*} [NormedField F]

private theorem isClosed_centralizer (γ : GL (Fin 2) F) :
    IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) F)) : Set (GL (Fin 2) F))) := by
  have h := isClosed_eq (continuous_id.mul continuous_const : Continuous fun x : GL (Fin 2) F => x * γ)
    (continuous_const.mul continuous_id : Continuous fun x : GL (Fin 2) F => γ * x)
  convert h using 1
  ext x
  exact Subgroup.mem_centralizer_singleton_iff

private theorem continuous_orbitMap (γ : GL (Fin 2) F) :
    Continuous (fun x : GL (Fin 2) F => x⁻¹ * γ * x) :=
  (continuous_inv.mul continuous_const).mul continuous_id

private theorem orbitMap_mul_left (γ : GL (Fin 2) F)
    (t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) F))) (x : GL (Fin 2) F) :
    ((t : GL (Fin 2) F) * x)⁻¹ * γ * ((t : GL (Fin 2) F) * x) = x⁻¹ * γ * x := by
  have ht : γ * (t : GL (Fin 2) F) = (t : GL (Fin 2) F) * γ :=
    (Subgroup.mem_centralizer_singleton_iff.mp t.2).symm
  calc ((t : GL (Fin 2) F) * x)⁻¹ * γ * ((t : GL (Fin 2) F) * x)
      = x⁻¹ * ((↑t)⁻¹ * (γ * ↑t)) * x := by group
    _ = x⁻¹ * ((↑t)⁻¹ * (↑t * γ)) * x := by rw [ht]
    _ = x⁻¹ * γ * x := by group

end S30UntwistedSection

open NumberField MeasureTheory AutomorphicForm
open scoped Pointwise

theorem solution
    (K : Type) [Field K] [NumberField K] (v : NumberField.InfinitePlace K)
    (μ : @Measure (GL (Fin 2) v.Completion) (glBorelOf v.Completion))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf v.Completion) μ)
    (γ : GL (Fin 2) v.Completion) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) v.Completion))) (centralizerBorel v.Completion γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion γ) τ)
    (f : GL (Fin 2) v.Completion → ℂ) (hfm : Measurable[glBorelOf v.Completion] f)
    (hfc : HasCompactSupport f) (hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) :
    (∃ w : GL (Fin 2) v.Completion → ℝ, IsSectionFnOn v.Completion γ τ f w ∧ Continuous w) ∧
      ∀ w : GL (Fin 2) v.Completion → ℝ, IsSectionFnOn v.Completion γ τ f w →
        ∀ I : ℂ, IsOrbitalIntegralOn v.Completion μ γ τ f I ↔
          I = @integral _ ℂ _ _ (glBorelOf v.Completion) μ fun x => f (x⁻¹ * γ * x) * (w x : ℂ) := by
  classical
  letI hmG : MeasurableSpace (GL (Fin 2) v.Completion) := AutomorphicForm.glBorelOf v.Completion
  haveI : BorelSpace (GL (Fin 2) v.Completion) := AutomorphicForm.borelSpace_glBorelOf v.Completion
  haveI : T2Space (Matrix (Fin 2) (Fin 2) v.Completion) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → v.Completion))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) v.Completion) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → v.Completion))
  haveI : LocallyCompactSpace (GL (Fin 2) v.Completion) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  letI hmT : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) v.Completion))) :=
    AutomorphicForm.centralizerBorel v.Completion γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) v.Completion))) := ⟨rfl⟩
  haveI : SecondCountableTopology v.Completion := by
    letI : NontriviallyNormedField v.Completion := M4aHerbrand.ArchSemilocal.nontriviallyNormedCompletion v
    haveI : ProperSpace v.Completion := ProperSpace.of_locallyCompactSpace v.Completion
    infer_instance
  haveI : SecondCountableTopology (GL (Fin 2) v.Completion) :=
    S30OrbitProperness.secondCountableTopology_gl v.Completion
  haveI : @Measure.IsHaarMeasure _ _ _ hmT τ := hτ
  haveI : τ.IsMulRightInvariant :=
    S30ArchSectionFn.isMulRightInvariant_of_forall_commute _ τ fun a b =>
      Subtype.ext (S30OrbitProperness.commute_of_mem_centralizer_of_isRegularSemisimple hγ a.2 b.2).eq
  obtain ⟨w, h0, hm, hc, h1, hw⟩ :=
    S30ArchSectionFn.exists_continuous_section (Subgroup.centralizer ({γ} : Set (GL (Fin 2) v.Completion))) τ
      (S30UntwistedSection.isClosed_centralizer γ) (S30UntwistedSection.continuous_orbitMap γ)
      (S30UntwistedSection.orbitMap_mul_left γ)
      (fun C hC => by
        obtain ⟨D, hD, hsub⟩ := S30OrbitProperness.isTwistedProper_id_of_isRegularSemisimple γ hγ C hC
        refine ⟨D, hD, ?_⟩
        rwa [AutomorphicForm.sigmaCentralizer_id] at hsub)
      hfc
  have hsec : AutomorphicForm.IsSectionFnOn v.Completion γ τ f w :=
    ⟨h0, hm, hc, fun x hx => h1 x (subset_tsupport f hx)⟩
  refine ⟨⟨w, hsec, hw⟩, fun w' hw' I => ⟨fun hI => ?_, fun h => ⟨w', hw', h⟩⟩⟩
  exact AutomorphicForm.IsOrbitalIntegralOn.unique_of_isRegularSemisimple v.Completion μ hμ γ hγ τ hτ f hfm hfb
    hI ⟨w', hw', rfl⟩

end S_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple
end P2MW
export P2MW.S_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple (solution)
