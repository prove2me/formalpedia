-- Prove2me | Definitions.Def_KadisonRingroseSupport2
-- name    : KadisonRingroseSupport2
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T14:36:25.95184+00:00
-- url     : https://prove2.me/theorems/3407a118-96ba-4700-be1a-3c4b03217510
-- title:
--   Bounded Hochschild vanishing: supporting development, part 2
-- statement:
--   Part 2 of the supporting Lean development for the vanishing of higher bounded Hochschild cohomology of von Neumann algebras. It continues part 1 with the definitions used by statements of the published child theorems: partial isometries, matrix systems, normal vectors and normal projections, corners, central averages, homogeneous projections, partial representations and word evaluation, cochain slices and prefix differentials, finite and type conditions on central summands, orbit hulls, operator factorizations, represented averaging orbits and normal GNS representations, in source order, together with the proved lemmas their bodies and instances rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies are proved here. The code is OpenAI's, carved from `lean/OAI/Analysis` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`. The `private` keyword is removed from declarations kept here so that later files can use them.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_KadisonRingrose
import Definitions.Def_KadisonRingroseSupport1

set_option linter.all false

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildDixmier
open BoundedHochschild HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

def gnsVector : M →ₗ[ℝ] τ.GNS :=
  (UniformSpace.Completion.toComplₗᵢ.toLinearMap.comp τ.toPreGNS.toLinearMap).restrictScalars ℝ

lemma gnsVector_norm (a : M) : ‖gnsVector τ a‖=‖τ.toPreGNS a‖ :=
  UniformSpace.Completion.norm_coe _

include e hL hτ in

theorem isClosed_gns_ball (C : ℝ) :
    IsClosed (gnsVector τ '' Metric.closedBall (0 : M) C) := by
  apply isSeqClosed_iff_isClosed.mp
  intro y z hy hz
  choose a ha hay using hy
  have hnorm : ∀ n, ‖a n‖ ≤ C := fun n => by simpa only [Metric.mem_closedBall,dist_zero_right] using ha n
  have hc : CauchySeq (fun n => τ.toPreGNS (a n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hz.cauchySeq ε hε
    refine ⟨N,fun m hm n hn => ?_⟩
    rw [dist_eq_norm,← map_sub,← gnsVector_norm τ, map_sub,hay m,hay n,← dist_eq_norm]
    exact hN m hm n hn
  obtain ⟨b,hb,ht⟩ := exists_bounded_preGNS_limit e τ hL hτ C hnorm hc
  have ht' : Tendsto (fun n => gnsVector τ (a n)) atTop (𝓝 (gnsVector τ b)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [← map_sub,gnsVector_norm] using ht
  have he : gnsVector τ b=z := tendsto_nhds_unique ht' (by simpa only [hay] using hz)
  exact ⟨b,by simpa only [Metric.mem_closedBall,dist_zero_right] using hb,he⟩

def conjugate (u : unitary M) : M →ₗ[ℝ] M where
  toFun a := (u : M)*a*star (u : M)
  map_add' := by intro a b; simp only [mul_add,add_mul]
  map_smul' := by intro r a; simp only [mul_smul_comm,smul_mul_assoc,RingHom.id_apply]

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_apply (u : unitary M) (a : M) :
    conjugate u a=(u : M)*a*star (u : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_norm (u : unitary M) (a : M) : ‖conjugate u a‖=‖a‖ := by
  change ‖(u : M)*a*(star u : unitary M)‖=‖a‖
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_mul (u v : unitary M) (a : M) : conjugate u (conjugate v a)=conjugate (u*v) a := by
  simp only [conjugate_apply,Submonoid.coe_mul,star_mul,mul_assoc]

lemma conjugate_gns_norm (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (u : unitary M) (a : M) :
    ‖gnsVector τ (conjugate u a)‖=‖gnsVector τ a‖ := by
  rw [gnsVector_norm,gnsVector_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow,Complex.ofReal_pow,τ.preGNS_norm_sq,τ.preGNS_norm_sq]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,conjugate_apply,star_mul,star_star]
  have he : (u : M)*(star a*star (u : M))*((u : M)*a*star (u : M))=
      (u : M)*(star a*a)*star (u : M) := by
    calc
      _ = (u : M)*(star a*((star (u : M)*(u : M))*a))*star (u : M) := by noncomm_ring
      _ = _ := by rw [Unitary.star_mul_self_of_mem u.prop,one_mul]
  rw [he,htr,← mul_assoc,Unitary.star_mul_self_of_mem u.prop,one_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma conjugate_hull (a : M) (u : unitary M) :
    conjugate u '' convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) := by
  rw [LinearMap.image_convexHull]
  apply convexHull_mono
  rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
  exact ⟨u*v,(conjugate_mul u v a).symm⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma orbit_hull_bounded (a : M) :
    convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      Metric.closedBall (0 : M) ‖a‖ := by
  apply convexHull_min _ (convex_closedBall _ _)
  rintro _ ⟨v,rfl⟩
  simp only [Metric.mem_closedBall,dist_zero_right,conjugate_norm,le_refl]

include e hL hτ in

theorem orbit_closure_lift (a : M) {z : τ.GNS}
    (hz : z ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) :
    ∃ b : M, ‖b‖ ≤ ‖a‖ ∧ gnsVector τ b=z := by
  have hsub : closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) ⊆
      gnsVector τ '' Metric.closedBall (0 : M) ‖a‖ :=
    closure_minimal (Set.image_mono (orbit_hull_bounded a)) (isClosed_gns_ball e τ hL hτ ‖a‖)
  obtain ⟨b,hb,hbz⟩ := hsub hz
  exact ⟨b,by simpa only [Metric.mem_closedBall,dist_zero_right] using hb,hbz⟩

lemma conjugate_mem_orbit_closure (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (a b : M)
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) (u : unitary M) :
    gnsVector τ (conjugate u b) ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hb
  choose c hc hcy using hy
  have ht : Tendsto (fun n => gnsVector τ (conjugate u (c n))) atTop
      (𝓝 (gnsVector τ (conjugate u b))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [← map_sub,conjugate_gns_norm τ htr]
    have hh := (tendsto_iff_norm_sub_tendsto_zero.mp hyt)
    simpa only [← hcy,← map_sub] using hh
  apply isClosed_closure.mem_of_tendsto ht
  exact Filter.Eventually.of_forall fun n => subset_closure
    ⟨conjugate u (c n),conjugate_hull a u ⟨c n,hc n,rfl⟩,rfl⟩

lemma orbit_gns_convex (a : M) :
    Convex ℝ (closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) := by
  exact ((convex_convexHull ℝ _).linear_image (gnsVector τ)).closure

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma exists_min_norm {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K) (hc : Convex ℝ K) :
    ∃ z ∈ K, ∀ w ∈ K, ‖z‖ ≤ ‖w‖ := by
  obtain ⟨z,hz,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hc 0
  refine ⟨z,hz,fun w hw => ?_⟩
  simp only [zero_sub,norm_neg] at hmin
  rw [hmin]
  apply ciInf_le (f := fun w : K => ‖(w : H)‖) _ ⟨w,hw⟩
  exact ⟨(0 : ℝ),by rintro _ ⟨v,rfl⟩; exact norm_nonneg _⟩

omit [CompleteSpace H] in
lemma min_norm_unique {K : Set H} (hc : Convex ℝ K) {z w : H} (hz : z ∈ K) (hw : w ∈ K)
    (hmin : ∀ y ∈ K, ‖z‖ ≤ ‖y‖) (he : ‖w‖=‖z‖) : w=z := by
  have hm := hmin ((1/2 : ℝ) • z+(1/2 : ℝ) • w)
    (hc hz hw (by norm_num) (by norm_num) (by norm_num))
  rw [← smul_add,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)] at hm
  have hsq : (2*‖z‖)^2 ≤ ‖z+w‖^2 := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr
    linarith
  have hp := parallelogram_law_with_norm ℝ z w
  rw [he] at hp
  have hz0 : ‖z-w‖=0 := by nlinarith [sq_nonneg ‖z-w‖,norm_nonneg (z-w)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz0)).symm
end Hilbert

include e hL hτ in

theorem exists_central_average (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ x : M, τ (star x*x)=0 → x=0) (a : M) :
    ∃ b : M, ‖b‖ ≤ ‖a‖ ∧ (∀ x : M, Commute b x) ∧
      gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
        (Set.range (fun v : unitary M => conjugate v a))) := by
  let := InnerProductSpace.rclikeToReal ℂ τ.GNS
  let K := closure (gnsVector τ '' convexHull ℝ
    (Set.range (fun v : unitary M => conjugate v a)))
  have hne : K.Nonempty := ⟨gnsVector τ (conjugate 1 a),
    subset_closure ⟨conjugate 1 a,subset_convexHull ℝ _ ⟨1,rfl⟩,rfl⟩⟩
  obtain ⟨z,hz,hmin⟩ := exists_min_norm hne isClosed_closure (orbit_gns_convex τ a)
  obtain ⟨b,hb,hbz⟩ := orbit_closure_lift e τ hL hτ a hz
  have hbmem : gnsVector τ b ∈ K := hbz ▸ hz
  have hfix : ∀ u : unitary M, conjugate u b=b := by
    intro u
    have he : gnsVector τ (conjugate u b)=gnsVector τ b := by
      apply min_norm_unique (orbit_gns_convex τ a) hbmem
        (conjugate_mem_orbit_closure τ htr a b hbmem u)
      · intro y hy; rw [hbz]; exact hmin y hy
      · exact conjugate_gns_norm τ htr u b
    apply sub_eq_zero.mp
    apply (preGNS_norm_eq_zero_iff τ hfaith _).mp
    rw [← gnsVector_norm τ,map_sub,he,sub_self,norm_zero]
  have hucomm : ∀ u : unitary M, Commute b (u : M) := by
    intro u
    have he := congrArg (fun x : M => x*(u : M)) (hfix u)
    simp only [conjugate_apply,mul_assoc,Unitary.star_mul_self_of_mem u.prop,mul_one] at he
    exact he.symm
  refine ⟨b,hb,?_,hbmem⟩
  intro x
  have hx : x ∈ Submodule.span ℂ (unitary M : Set M) := by
    rw [CStarAlgebra.span_unitary]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact hucomm ⟨y,hy⟩
  | zero => exact Commute.zero_right b
  | add y z hy hz ihy ihz => exact ihy.add_right ihz
  | smul r y hy ih => exact ih.smul_right r
end HochschildDixmier
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M]

structure PartialIso (M : Type*) [CStarAlgebra M] where
  val : M
  mul_star_mul : val * star val * val = val

namespace PartialIso
instance : Coe (PartialIso M) M := ⟨val⟩
@[ext] lemma ext {v w : PartialIso M} (h : (v : M) = w) : v = w := by
  cases v; cases w; congr

def initial (v : PartialIso M) : M := star (v : M) * v
def final (v : PartialIso M) : M := (v : M) * star (v : M)
lemma mul_initial (v : PartialIso M) : (v : M) * v.initial = v := by
  simpa only [initial, ← mul_assoc] using v.mul_star_mul

lemma initial_proj (v : PartialIso M) : IsStarProjection v.initial := by
  refine ⟨?_, IsSelfAdjoint.star_mul_self _⟩
  change (star (v : M) * v) * (star (v : M) * v) = star (v : M) * v
  calc
    _ = star (v : M) * ((v : M) * star (v : M) * v) := by simp only [mul_assoc]
    _ = _ := by rw [v.mul_star_mul]

variable [PartialOrder M]

instance : LE (PartialIso M) := ⟨fun v w => v.initial ≤ w.initial ∧ (w : M) * v.initial = v⟩

variable [StarOrderedRing M]

instance : PartialOrder (PartialIso M) where
  le_refl v := ⟨le_rfl, v.mul_initial⟩
  le_trans v w z hvw hwz := by
    refine ⟨hvw.1.trans hwz.1, ?_⟩
    calc
      (z : M) * v.initial = (z : M) * (w.initial * v.initial) := by
        rw [(v.initial_proj.le_iff_mul_eq_right w.initial_proj).mp hvw.1]
      _ = (w : M) * v.initial := by rw [← mul_assoc,hwz.2]
      _ = v := hvw.2
  le_antisymm v w hvw hwv := by
    apply ext
    have he := le_antisymm hvw.1 hwv.1
    have hh := hvw.2
    rw [he, w.mul_initial] at hh
    exact hh.symm

instance : Zero (PartialIso M) := ⟨⟨0, by simp⟩⟩
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma coe_zero : ((0 : PartialIso M) : M) = 0 := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma initial_zero : (0 : PartialIso M).initial = 0 := by simp [initial]
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma final_zero : (0 : PartialIso M).final = 0 := by simp [final]
end PartialIso
end HochschildComparison
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

structure MatrixSystem (M : Type*) [Ring M] [StarRing M] (n : ℕ) where
  entry : Fin n → Fin n → M
  star_entry : ∀ i j, star (entry i j)=entry j i
  entry_mul : ∀ i j k l, entry i j*entry k l=if j=k then entry i l else 0
  sum_diagonal : ∑ i, entry i i=1
end HochschildMatrixSystems
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def predualEmbedding : X →ₗᵢ⋆[ℂ] StrongDual ℂ M where
  toFun z := (starL ℂ).toContinuousLinearMap.comp (((ContinuousLinearMap.apply ℂ ℂ) z).comp
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  map_add' z w := by ext a; simp
  map_smul' r z := by ext a; simp
  norm_map' z := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro a
      change ‖star (e.symm a z)‖ ≤ ‖z‖*‖a‖
      simpa only [norm_star,e.symm.norm_map,mul_comm] using (e.symm a).le_opNorm z
    · apply NormedSpace.norm_le_dual_bound ℂ z (norm_nonneg _)
      intro f
      have := ((starL ℂ).toContinuousLinearMap.comp (((ContinuousLinearMap.apply ℂ ℂ) z).comp
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap)).le_opNorm (e f)
      change ‖f z‖ ≤ ‖(starL ℂ).toContinuousLinearMap.comp
        (((ContinuousLinearMap.apply ℂ ℂ) z).comp
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖ * ‖f‖
      simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
        ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        starL_apply,e.symm_apply_apply,norm_star,e.norm_map] using this

@[simp] lemma predualEmbedding_apply (z : X) (a : M) :
    predualEmbedding e z a=star (e.symm a z) := rfl

def normalDual : Submodule ℂ (StrongDual ℂ M) := (predualEmbedding e).toLinearMap.range

lemma mem_normalDual (φ : StrongDual ℂ M) :
    φ ∈ normalDual e ↔ ∃ z : X, ∀ a : M, φ a=star (e.symm a z) := by
  constructor
  · rintro ⟨z,rfl⟩; exact ⟨z,fun _ => rfl⟩
  · rintro ⟨z,hz⟩; exact ⟨z,ContinuousLinearMap.ext (fun a => (hz a).symm)⟩

variable [CompleteSpace X]

lemma normalDual_closed : IsClosed (normalDual e : Set (StrongDual ℂ M)) :=
  (predualEmbedding e).isometry.isClosedEmbedding.isClosed_range

omit [CompleteSpace X] in
lemma normalDual_comp {φ : StrongDual ℂ M} (hφ : φ ∈ normalDual e)
    (L : M →L[ℂ] M) (hL : BoundedHochschild.HasPreadjoint e L) :
    φ.comp L ∈ normalDual e := by
  obtain ⟨z,hz⟩ := (mem_normalDual e φ).mp hφ
  obtain ⟨w,hw⟩ := hL z
  exact (mem_normalDual e _).mpr ⟨w,fun a => by simp only [ContinuousLinearMap.comp_apply,hz,hw]⟩

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))

def coefficient (η : H) : H →L[ℂ] StrongDual ℂ M := by
  let L : H →ₗ[ℂ] StrongDual ℂ M :=
    { toFun := fun ξ => (innerSL ℂ η).comp
        (((ContinuousLinearMap.apply ℂ H) ξ).comp (π.toAlgHom.toLinearMap.mkContinuous 1 (fun a => by simpa using NonUnitalStarAlgHom.norm_apply_le π a)))
      map_add' := by intro ξ ζ; ext a; simp
      map_smul' := by intro r ξ; ext a; simp }
  exact L.mkContinuous ‖η‖ (by
    intro ξ
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro a
    change ‖⟪η,π a ξ⟫_ℂ‖ ≤ (‖η‖*‖ξ‖)*‖a‖
    calc
      _ ≤ ‖η‖*‖π a ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖η‖*(‖π a‖*‖ξ‖) := mul_le_mul_of_nonneg_left ((π a).le_opNorm ξ) (norm_nonneg _)
      _ ≤ ‖η‖*(‖a‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
      _ = _ := by ring)

@[simp] lemma coefficient_apply (η ξ : H) (a : M) :
    coefficient π η ξ a=⟪η,π a ξ⟫_ℂ := rfl

def normalVectors : Submodule ℂ H := ⨅ η : H, (normalDual e).comap (coefficient π η).toLinearMap

omit [CompleteSpace X] in
lemma mem_normalVectors (ξ : H) :
    ξ ∈ normalVectors e π ↔ ∀ η, coefficient π η ξ ∈ normalDual e := by
  simp only [normalVectors,Submodule.mem_iInf,Submodule.mem_comap,ContinuousLinearMap.coe_coe]

lemma normalVectors_closed : IsClosed (normalVectors e π : Set H) := by
  have hs : (normalVectors e π : Set H)=⋂ η : H, (coefficient π η) ⁻¹' (normalDual e : Set (StrongDual ℂ M)) := by
    ext ξ; simp only [Set.mem_iInter,Set.mem_preimage,SetLike.mem_coe,mem_normalVectors]
  rw [hs]
  exact isClosed_iInter fun η => (normalDual_closed e).preimage (coefficient π η).continuous

instance normalVectors_complete : CompleteSpace (normalVectors e π) :=
  (normalVectors_closed e π).completeSpace_coe

lemma normalVectors_mul {ξ : H} (hξ : ξ ∈ normalVectors e π) (b : M) :
    π b ξ ∈ normalVectors e π := by
  rw [mem_normalVectors] at hξ ⊢
  intro η
  have hc : coefficient π η (π b ξ) =
      (coefficient π η ξ).comp ((ContinuousLinearMap.mul ℂ M).flip b) := by
    ext a; simp [map_mul]
  rw [hc]
  exact normalDual_comp e (hξ η) _ ((HochschildSakai.abstract_multiplication_normal e).2 b)

def normalProjection : H →L[ℂ] H := (normalVectors e π).starProjection

end HochschildNormalPart

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v w
variable {M : Type u} [CStarAlgebra M]
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def sumOperator (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    ((T.prodMap S).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toContinuousLinearMap)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] lemma sumOperator_apply (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : WithLp 2 (H×K)) :
    sumOperator T S x=WithLp.toLp 2 (T x.fst,S x.snd) := rfl

def sumRepresentation (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    M →⋆ₐ[ℂ] (WithLp 2 (H×K) →L[ℂ] WithLp 2 (H×K)) where
  toFun a := sumOperator (π a) (ρ a)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp; rfl
  map_add' a b := by ext x; simp; rfl
  map_mul' a b := by ext x; simp [map_mul,mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]; rfl
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [sumOperator_apply,WithLp.prod_inner_apply,
      map_star,ContinuousLinearMap.star_eq_adjoint]
    simp only [ContinuousLinearMap.adjoint_inner_left]
    rfl

@[simp] lemma sumRepresentation_apply (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : M) (x : WithLp 2 (H×K)) :
    sumRepresentation π ρ a x=WithLp.toLp 2 (π a x.fst,ρ a x.snd) := rfl
end HochschildNormalPart
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def corner (p : M) (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ M where
  carrier := {a | p*a=a ∧ a*p=a}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    exact ⟨by rw [mul_add,ha,hb],by rw [add_mul,ha',hb']⟩
  mul_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    exact ⟨by rw [← mul_assoc,ha],by rw [mul_assoc,hb']⟩
  smul_mem' := by
    intro c a ha
    exact ⟨by rw [mul_smul_comm,ha.1],by rw [smul_mul_assoc,ha.2]⟩
  star_mem' := by
    intro a ha
    exact ⟨by simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha.2,
      by simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha.1⟩

instance corner_closed (p : M) (hp : IsStarProjection p) : IsClosed (corner p hp : Set M) := by
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

omit [PartialOrder M] [StarOrderedRing M] in
lemma self_mem_corner {p : M} (hp : IsStarProjection p) : p ∈ corner p hp :=
  ⟨hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end HochschildCorners

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild BoundedHochschild.WeakAlgebra HochschildRigidity HochschildSakai
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p)

abbrev Corner := corner p hp

instance cornerOne : One (Corner p hp) := ⟨⟨p,self_mem_corner hp⟩⟩
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_one : ((1 : Corner p hp):M)=p := rfl

instance cornerRing : Ring (Corner p hp) where
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2
  natCast := fun n => ⟨n • p,(corner p hp).nsmul_mem (self_mem_corner hp) n⟩
  natCast_zero := Subtype.ext (zero_nsmul _)
  natCast_succ n := Subtype.ext (succ_nsmul _ _)
  intCast := fun z => ⟨z • p,(corner p hp).toNonUnitalSubring.toAddSubgroup.zsmul_mem (self_mem_corner hp) z⟩
  intCast_ofNat n := Subtype.ext (natCast_zsmul _ _)
  intCast_negSucc n := Subtype.ext (negSucc_zsmul _ _)

instance cornerAlgebra : Algebra ℂ (Corner p hp) where
  algebraMap :=
    { toFun := fun c => c • (1 : Corner p hp)
      map_zero' := zero_smul _ _
      map_one' := one_smul _ _
      map_add' := fun _ _ => add_smul _ _ _
      map_mul' := fun c d => by
        ext
        change (c*d) • p=(c • p)*(d • p)
        rw [smul_mul_smul_comm,hp.isIdempotentElem.eq] }
  commutes' c a := by
    ext
    change (c • p)*(a:M)=(a:M)*(c • p)
    rw [smul_mul_assoc,mul_smul_comm,a.property.1,a.property.2]
  smul_def' c a := by
    ext
    change c • (a:M)=(c • p)*(a:M)
    rw [smul_mul_assoc,a.property.1]

instance cornerNormedRing : NormedRing (Corner p hp) where
  dist_eq a b := by
    change dist (a:M) (b:M)=‖-(a:M)+(b:M)‖
    rw [dist_comm,dist_eq_norm,sub_eq_add_neg,add_comm]
  norm_mul_le a b := norm_mul_le (a:M) (b:M)
instance cornerNormedAlgebra : NormedAlgebra ℂ (Corner p hp) where
  norm_smul_le c a := norm_smul_le c (a:M)
instance cornerCStarAlgebra : CStarAlgebra (Corner p hp) where

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_mul (a b : Corner p hp) : ((a*b : Corner p hp):M)=(a:M)*(b:M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_star (a : Corner p hp) : ((star a : Corner p hp):M)=star (a:M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_smul (c : ℂ) (a : Corner p hp) : ((c • a : Corner p hp):M)=c • (a:M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_zero : ((0 : Corner p hp):M)=0 := rfl

instance cornerStarOrderedRing : StarOrderedRing (Corner p hp) :=
  StarOrderedRing.of_nonneg_iff' (fun {a b} h c => show (c:M)+(a:M) ≤ (c:M)+(b:M) from add_le_add le_rfl (show (a:M) ≤ (b:M) from h))
    (fun a => by
      constructor
      · intro ha
        have haM : (0:M) ≤ (a:M) := ha
        have hs : CFC.sqrt (a:M) ∈ corner p hp := by
          rw [CFC.sqrt_eq_real_sqrt (a:M) haM]
          exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
        refine ⟨⟨CFC.sqrt (a:M),hs⟩,Subtype.ext ?_⟩
        change (a:M)=star (CFC.sqrt (a:M))*CFC.sqrt (a:M)
        rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq,CFC.sqrt_mul_sqrt_self (a:M) haM]
      · rintro ⟨b,rfl⟩
        exact star_mul_self_nonneg (b:M))
end HochschildCorners
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
namespace HochschildNormalPart
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

structure FunctionalModel (φ : StrongDual ℂ M) where
  H : Type u
  [normed : NormedAddCommGroup H]
  [innerSpace : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  representation : M →⋆ₐ[ℂ] (H →L[ℂ] H)
  leftVector : H
  rightVector : H
  realizes : coefficient representation leftVector rightVector=φ
  bound : ‖leftVector‖*‖rightVector‖≤4*‖φ‖
attribute [instance] FunctionalModel.normed FunctionalModel.innerSpace FunctionalModel.complete
end HochschildNormalPart
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

def algebra : NonUnitalStarSubalgebra ℂ M where
  carrier := {a | p*a=a ∧ a*p=a}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    change p*(a+b)=a+b ∧ (a+b)*p=a+b
    simp only [mul_add,add_mul,ha,ha',hb,hb',and_self]
  mul_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    change p*(a*b)=a*b ∧ (a*b)*p=a*b
    constructor
    · rw [←mul_assoc,ha]
    · rw [mul_assoc,hb']
  smul_mem' := by
    rintro c a ⟨ha,ha'⟩
    change p*(c • a)=c • a ∧ (c • a)*p=c • a
    simp only [mul_smul_comm,smul_mul_assoc,ha,ha',and_self]
  star_mem' := by
    rintro a ⟨ha,ha'⟩
    constructor
    · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha'
    · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha

instance algebra_closed : IsClosed (algebra hp : Set M) :=
  (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

instance instOne : One (algebra hp) := ⟨⟨p,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩⟩
instance instRing : Ring (algebra hp) where
  __ := (inferInstance : NonUnitalRing (algebra hp))
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2

instance instAlgebra : Algebra ℂ (algebra hp) := Algebra.ofModule
  (fun c a b => smul_mul_assoc c a b) (fun c a b => by rw [mul_smul_comm])
instance instNormedRing : NormedRing (algebra hp) where
  __ := (inferInstance : NonUnitalNormedRing (algebra hp))
  __ := instRing hp
instance instNormedAlgebra : NormedAlgebra ℂ (algebra hp) where
  norm_smul_le c x := norm_smul_le c x
instance instCStarAlgebra : CStarAlgebra (algebra hp) where

instance instStarOrderedRing : StarOrderedRing (algebra hp) := by
  apply StarOrderedRing.of_nonneg_iff'
  · intro x y h z
    change (z:M)+(x:M) ≤ (z:M)+(y:M)
    simpa only [add_comm] using add_le_add_left (show (x:M) ≤ (y:M) from h) (z:M)
  · intro a
    constructor
    · intro ha
      have hmem : CFC.sqrt (a:M) ∈ algebra hp := by
        rw [CFC.sqrt_eq_real_sqrt (a:M) (show 0 ≤ (a:M) from ha)]
        exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
      refine ⟨⟨CFC.sqrt (a:M),hmem⟩,Subtype.ext ?_⟩
      change (a:M)=star (CFC.sqrt (a:M))*CFC.sqrt (a:M)
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a:M))).star_eq]
      exact (CFC.sqrt_mul_sqrt_self (a:M) ha).symm
    · rintro ⟨b,rfl⟩
      exact star_mul_self_nonneg (b:M)

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma coe_one : ((1 : algebra hp):M)=p := rfl

end PopaCorner

namespace PopaCorner
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

def compress (x : M) : algebra hp := ⟨p*x*p,by
  constructor
  · rw [←mul_assoc,←mul_assoc,hp.isIdempotentElem.eq]
  · rw [mul_assoc,hp.isIdempotentElem.eq]⟩
end PopaCorner
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def NoAbelianCorners (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] : Prop :=
  ∀ (p : M) (hp : IsStarProjection p), p ≠ 0 →
    ∃ a b : PopaCorner.algebra hp, ¬ Commute a b
end PopaTypeII
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def Central (a : M) : Prop := ∀ x : M, Commute a x

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

def average (a : M) : M := (exists_central_average e τ
  (HochschildSakai.abstract_multiplication_normal e).1 hτ htr hfaith a).choose
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaCorners
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

section Dual
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

structure System (n : ℕ) (p : M) where
  entry : Fin n → Fin n → M
  star_entry : ∀ i j, star (entry i j)=entry j i
  mul_entry : ∀ i j k l, entry i j*entry k l=if j=k then entry i l else 0
  sum_diag : ∑ i, entry i i=p
end Dual
end PopaMatrices
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ}
namespace System
variable (s : System n (1:M))

def sumExpect (x : M) : M := ∑ i, ∑ j, s.entry i j*x*s.entry j i

def expect (x : M) : M := (n : ℝ)⁻¹ • s.sumExpect x
end System
end PopaMatrices
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

def Homogeneous (p : M) : Prop := average e τ hτ htr hfaith p=(τ p).re • (1:M)
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
variable (G M : Type*) [Group G] [CStarAlgebra M]

structure Rep where
  val : G → M
  mul : ∀ g h, val (g*h)=val g*val h
  inv : ∀ g, val g⁻¹=star (val g)

namespace Rep
variable {G M} [PartialOrder M] [StarOrderedRing M]

instance : CoeFun (Rep G M) (fun _ => G → M) := ⟨Rep.val⟩
end Rep
end PopaPatching
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaPatching
open BoundedHochschild HochschildRigidity
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

abbrev Letter (C B : Type*) := C ⊕ B

def letterValue (a : C → M) (γ : B → G) (v : Rep G M) : Letter C B → M :=
  Sum.elim a (fun b => v (γ b))

def evaluate (a : C → M) (γ : B → G) (v : Rep G M) (l : List (Letter C B)) : M :=
  (l.map (letterValue a γ v)).prod

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma evaluate_nil (a : C → M) (γ : B → G) (v : Rep G M) : evaluate a γ v []=1 := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma evaluate_cons (a : C → M) (γ : B → G) (v : Rep G M) (x) (l) :
    evaluate a γ v (x::l)=letterValue a γ v x*evaluate a γ v l := rfl
end PopaPatching
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {p : M} (hp : IsStarProjection p) (τ : M →ₚ[ℂ] ℂ)

def trace : algebra hp →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀
  ((((τ p).re⁻¹ : ℝ) : ℂ) • τ.toLinearMap.comp (algebra hp).toNonUnitalSubalgebra.toSubmodule.subtype) (by
    intro a ha
    change 0 ≤ (((τ p).re⁻¹ : ℝ) : ℂ)*τ (a:M)
    apply mul_nonneg
    · exact Complex.nonneg_iff.mpr ⟨inv_nonneg.mpr
        (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1,rfl⟩
    · exact τ.map_nonneg ha)

@[simp] lemma trace_apply (a : algebra hp) :
    trace hp τ a=(((τ p).re⁻¹ : ℝ) : ℂ)*τ (a:M) := rfl
end PopaCorner
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaMatrices

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaMatrices

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaCorner

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

def cornerCoefficient {p : M} (_hp : IsStarProjection p) (a : M) : M :=
  (τ p).re⁻¹ • average e τ hτ htr hfaith (p*a*p)
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoAbelianCorners M)

include e τ hτ htr hfaith h1 hII

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace PopaSeparable
open BoundedHochschild PopaCenter PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
variable (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

end PopaSeparable

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoAbelianCorners M)
include e hτ htr hfaith h1 hII

end BoundedHochschild

open scoped ComplexOrder
namespace PopaTypeII
open BoundedHochschild PopaCenter PopaCorner PopaCorners
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def AbelianProjection {p : M} (hp : IsStarProjection p) : Prop :=
  ∀ a b : algebra hp, Commute a b

def TypeICorner {z : M} (_hz : IsStarProjection z) : Prop :=
  ∀ p : M, ∀ _hp : IsStarProjection p, p ≤ z → p ≠ 0 →
    ∃ q : M, ∃ hq : IsStarProjection q, q ≤ p ∧ q ≠ 0 ∧ AbelianProjection hq

def NoTypeICentralPart (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] : Prop :=
  ∀ z : M, ∀ hz : IsStarProjection z, Central z → z ≠ 0 → ¬ TypeICorner hz
end PopaTypeII
end
end OAI
end

section
namespace OAI

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def sliceAt {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1))
    (v : Fin n → M) : M →L[ℂ] M := (f.curryMid i).flipMultilinear v

@[simp] lemma sliceAt_apply {n : ℕ} (f : Cochain M (n+1)) (i : Fin (n+1))
    (v : Fin n → M) (a : M) : sliceAt f i v a=f (i.insertNth a v) := rfl

def NormalBefore {n : ℕ} (f : Cochain M (n+1)) (r : ℕ) : Prop :=
  ∀ i : Fin (n+1), i.val<r → ∀ v,HasPreadjoint e (sliceAt f i v)

def UnitZeroBefore {n : ℕ} (f : Cochain M (n+1)) (r : ℕ) : Prop :=
  ∀ i : Fin (n+1), i.val<r → ∀ v,f (i.insertNth 1 v)=0

def prefixDifferential : {n : ℕ} → Cochain M n → ℕ → Cochain M (n+1)
  | 0,h,_ => leftCoboundary h
  | n+1,h,r => leftCoboundary h + ∑ j : Fin (n+1),if j.val<r then
      ((-1:ℂ)^(j.val+1)) • middleCoboundary h j else 0

@[simp] lemma prefixDifferential_apply {n : ℕ} (h : Cochain M n) (r : ℕ)
    (v : Fin (n+1) → M) :
    prefixDifferential h r v=v 0*h (fun i => v i.succ) +
      ∑ j : Fin n,if j.val<r then ((-1:ℂ)^(j.val+1)) • h (mergeInputs v j) else 0 := by
  cases n with
  | zero => simp [prefixDifferential]
  | succ n =>
    simp only [prefixDifferential,add_apply,leftCoboundary_apply,sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [smul_apply,middleCoboundary_apply,zero_apply]
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace HochschildNormalPart
universe u
variable (M : Type u) [CStarAlgebra M]

structure SharedHilbertFactor (B : M →L[ℂ] StrongDual ℂ M) where
  H : Type u
  group : NormedAddCommGroup H
  inner : InnerProductSpace ℂ H
  complete : CompleteSpace H
  left : H →L[ℂ] StrongDual ℂ M
  right : M →L[ℂ] H
  pairing : ∀ a b,B a b=left (right b) a

attribute [instance] SharedHilbertFactor.group SharedHilbertFactor.inner SharedHilbertFactor.complete

end HochschildNormalPart

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def SeparatelyNormal {M X : Type*} [CStarAlgebra M]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ} (f : Cochain M n) : Prop :=
  ∀ (i : Fin n) (v : Fin n → M) (z : X), ∃ w : X,
    ∀ a : M, e.symm (f (Function.update v i a)) z=e.symm a w
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace HochschildDomination
universe u v
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

@[nolint unusedArguments]
def PreHilbert (_φ _ψ : M →ₚ[ℂ] ℂ) := M

namespace PreHilbert
variable (φ ψ : M →ₚ[ℂ] ℂ)
instance : AddCommGroup (PreHilbert φ ψ) := inferInstanceAs (AddCommGroup M)
instance : Module ℂ (PreHilbert φ ψ) := inferInstanceAs (Module ℂ M)

def of : M ≃ₗ[ℂ] PreHilbert φ ψ := LinearEquiv.refl ℂ _
def val : PreHilbert φ ψ ≃ₗ[ℂ] M := LinearEquiv.refl ℂ _

omit [StarOrderedRing M] in
@[simp] lemma of_val (x : PreHilbert φ ψ) : of φ ψ (val φ ψ x) = x := rfl
omit [StarOrderedRing M] in
@[simp] lemma val_of (x : M) : val φ ψ (of φ ψ x) = x := rfl

abbrev core : PreInnerProductSpace.Core ℂ (PreHilbert φ ψ) where
  inner x y := φ (star (val φ ψ x) * val φ ψ y) +
    ψ (val φ ψ y * star (val φ ψ x))
  conj_inner_symm := by
    intro x y
    simp [← Complex.star_def, ← map_star φ, ← map_star ψ, star_add]
  re_inner_nonneg x := by
    exact add_nonneg (Complex.nonneg_iff.mp (φ.map_nonneg (star_mul_self_nonneg _))).1
      (Complex.nonneg_iff.mp (ψ.map_nonneg (mul_star_self_nonneg _))).1
  add_left := by
    intros
    simp only [map_add, star_add, add_mul, mul_add]
    ring
  smul_left := by
    intros
    simp only [map_smul, star_smul, smul_mul_assoc, mul_smul_comm, map_smul,
      smul_eq_mul, starRingEnd_apply, mul_add]

instance : SeminormedAddCommGroup (PreHilbert φ ψ) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := core φ ψ)
instance : InnerProductSpace ℂ (PreHilbert φ ψ) :=
  InnerProductSpace.ofCore (core φ ψ)
end PreHilbert
end HochschildDomination
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners
open scoped ComplexOrder

universe u

def FiniteAlgebra (N : Type u) [CStarAlgebra N] : Prop :=
  ∀ v : N, star v * v = 1 → v * star v = 1

def NoTypeII1Summand (N : Type u) [CStarAlgebra N]
    [PartialOrder N] [StarOrderedRing N] : Prop :=
  ∀ (z : N) (hz : IsStarProjection z), (∀ a : N, z * a = a * z) →
    FiniteAlgebra (Corner z hz) →
    PopaTypeII.NoTypeICentralPart (Corner z hz) → z = 0

def TracialTypeII (N : Type u) [CStarAlgebra N]
    [PartialOrder N] [StarOrderedRing N] : Prop :=
  ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X)
    (_ : CompleteSpace X) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (τ : N →ₚ[ℂ] ℂ),
    TraceInPredual e τ ∧ (∀ a b : N, τ (a * b) = τ (b * a)) ∧
    (∀ a : N, τ (star a * a) = 0 → a = 0) ∧ τ 1 = 1 ∧
    PopaTypeII.NoTypeICentralPart N

structure CentralDecomposition (M : Type u) [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] where
  Index : Type u
  projection : Option Index → M
  isProjection : ∀ i, IsStarProjection (projection i)
  central : ∀ i a, projection i * a = a * projection i
  orthogonal : ∀ i j, i ≠ j → projection i * projection j = 0
  total : ∀ x : M, (∀ i, projection i * x = 0) → x = 0
  exceptional : NoTypeII1Summand (Corner (projection none) (isProjection none))
  tracial : ∀ i, TracialTypeII (Corner (projection (some i)) (isProjection (some i)))

def CentralDecompositionInput (M : Type u) [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] : Prop :=
  Nonempty (CentralDecomposition M)

def ClassicalVanishingInput : Prop :=
  ∀ (N : Type u) [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N],
    WStarAlgebra N → NoTypeII1Summand N →
    ∀ (n : ℕ) (f : Cochain N (n + 2)),
      (∀ x, differentialValue f x = 0) →
      ∃ g : Cochain N (n + 1), ∀ x, differentialValue g x = f x
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def CentralProjection (p : M) : Prop :=
  IsStarProjection p ∧ ∀ a : M, Commute p a

def AbelianProjection (p : M) : Prop :=
  IsStarProjection p ∧ ∀ a b : M, Commute (p * a * p) (p * b * p)
end FinitePathMain
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def IsCentralSupport (p z : M) : Prop :=
  CentralProjection z ∧ p ≤ z ∧
    ∀ c : M, CentralProjection c → c * p = 0 → c * z = 0
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners HochschildComparison HochschildMatrixSystems FinitePathMain

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def HomogeneousTypeICorner (z : M) : Prop :=
  ∃ (hz : IsStarProjection z) (n : ℕ) (E : MatrixSystem (Corner z hz) n) (i : Fin n),
    AbelianProjection (E.entry i i)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def positiveFunctionalCLM (ψ : M →ₚ[ℂ] ℂ) : StrongDual ℂ M :=
  ⟨ψ.toLinearMap, map_continuous ψ⟩

def unitaryPullback (F : StrongDual ℂ M) (u : unitary M) : StrongDual ℂ M :=
  (F.comp ((ContinuousLinearMap.mul ℂ M).flip (star (u : M)))).comp
    (ContinuousLinearMap.mul ℂ M (u : M))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma unitaryPullback_apply (F : StrongDual ℂ M) (u : unitary M) (a : M) :
    unitaryPullback F u a = F ((u : M) * a * star (u : M)) := rfl

def unitaryOrbitHull (F : StrongDual ℂ M) : Set (StrongDual ℂ M) :=
  closure (convexHull ℝ (Set.range (unitaryPullback F)))
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def weakFunctionalClosure (K : Set (StrongDual ℂ M)) : Set (WeakDual ℂ M) :=
  closure (StrongDual.toWeakDual '' K)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

def weakPredualMap (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (x : WeakSpace ℂ X) : WeakDual ℂ M :=
  StrongDual.toWeakDual (predualEmbedding e ((toWeakSpace ℂ X).symm x))

@[simp] lemma weakPredualMap_apply (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (x : WeakSpace ℂ X) (a : M) :
    weakPredualMap e x a = star (e.symm a ((toWeakSpace ℂ X).symm x)) := rfl
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners

universe u

def NoFiniteCentralSummand (M : Type u) [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] : Prop :=
  ∀ (p : M) (hp : IsStarProjection p), (∀ a : M, p * a = a * p) →
    FiniteAlgebra (Corner p hp) → p = 0
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def countableMatrixAlgebra (c : ℕ → PartialIso M) : StarSubalgebra ℂ M :=
  StarAlgebra.adjoin ℂ (Set.range (fun p : ℕ × ℕ => (c p.1 : M) * star (c p.2 : M)))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

variable {I : Type*} [Fintype I]

def finiteRightAverage (m : I → M) (T : M →L[ℂ] M) : M →L[ℂ] M :=
  ∑ i, ((ContinuousLinearMap.mul ℂ M).flip (star (m i))).comp
    (T.comp ((ContinuousLinearMap.mul ℂ M).flip (m i)))

@[simp] lemma finiteRightAverage_apply (m : I → M) (T : M →L[ℂ] M) (a : M) :
    finiteRightAverage m T a = ∑ i, T (a * m i) * star (m i) := by
  simp only [finiteRightAverage, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def CompletelyBoundedEstimate (T : M →L[ℂ] M) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (A : CStarMatrix (Fin n) (Fin n) M), ‖A.map T‖ ≤ C * ‖A‖
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M X : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

def weakOperatorImage (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (T : M →L[ℂ] M) :
    M → WeakDual ℂ X := fun a => StrongDual.toWeakDual (e.symm (T a))

def weakOperatorBall (C : ℝ) : Set (M → WeakDual ℂ X) :=
  {F | (∀ a b, F (a + b) = F a + F b) ∧
    (∀ (z : ℂ) a, F (z • a) = star z • F a) ∧
    ∀ a, ‖WeakDual.toStrongDual (F a)‖ ≤ C * ‖a‖}
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

def rightAverageOrbit (T : M →L[ℂ] M) : Set (M →L[ℂ] M) :=
  {S | ∃ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) ∧
    S = finiteRightAverage m T}

universe u
variable {N X : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def weakRightAverageOrbit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (T : N →L[ℂ] N) :
    Set (N → WeakDual ℂ X) := closure (weakOperatorImage e '' rightAverageOrbit T)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def operatorSystemMatrices (S : Submodule ℂ A) (n : ℕ) :
    Submodule ℂ (CStarMatrix (Fin n) (Fin n) A) where
  carrier := {X | ∀ i j, X i j ∈ S}
  zero_mem' := fun _ _ => S.zero_mem
  add_mem' hX hY := fun i j => S.add_mem (hX i j) (hY i j)
  smul_mem' z _X hX := fun i j => S.smul_mem z (hX i j)

def operatorSystemAmplification {B : Type*} [CStarAlgebra B]
    (S : Submodule ℂ A) (φ : S →ₗ[ℂ] B) (n : ℕ) :
    operatorSystemMatrices S n →ₗ[ℂ] CStarMatrix (Fin n) (Fin n) B where
  toFun X := CStarMatrix.ofMatrix (fun i j => φ ⟨X.val i j, X.property i j⟩)
  map_add' X Y := by
    apply CStarMatrix.ext
    intro i j
    exact map_add φ ⟨X.val i j, X.property i j⟩ ⟨Y.val i j, Y.property i j⟩
  map_smul' z X := by
    apply CStarMatrix.ext
    intro i j
    exact map_smul φ z ⟨X.val i j, X.property i j⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

universe u v
variable {A : Type u} {H : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure OperatorFactorization (T : A →ₗ[ℂ] (H →L[ℂ] H)) (C : ℝ) where
  K : Type (max u v)
  [normed : NormedAddCommGroup K]
  [innerSpace : InnerProductSpace ℂ K]
  [complete : CompleteSpace K]
  representation : A →⋆ₐ[ℂ] (K →L[ℂ] K)
  leftMap : H →L[ℂ] K
  rightMap : H →L[ℂ] K
  bound : ‖leftMap‖ * ‖rightMap‖ ≤ C
  factorization : ∀ a, T a = leftMap.adjoint.comp ((representation a).comp rightMap)

attribute [instance] OperatorFactorization.normed OperatorFactorization.innerSpace
  OperatorFactorization.complete
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I H K : Type*} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def operatorRowAverage (a : I → (K →L[ℂ] K)) (b : I → (H →L[ℂ] H))
    (W : H →L[ℂ] K) : H →L[ℂ] K :=
  ∑ i, (a i).comp (W.comp (b i).adjoint)

omit [CompleteSpace K] in
@[simp] lemma operatorRowAverage_apply (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H)) (W : H →L[ℂ] K) (ξ : H) :
    operatorRowAverage a b W ξ = ∑ i, a i (W ((b i).adjoint ξ)) := by
  simp only [operatorRowAverage, sum_apply, ContinuousLinearMap.comp_apply]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped InnerProductSpace ComplexOrder ENNReal

namespace BoundedHochschild.KadisonRingrose

open HochschildNormalPart

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

abbrev UniversalGNS (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] :=
  lp (fun ψ : M →ₚ[ℂ] ℂ => ψ.GNS) 2

def universalGNSAction (a : M) (ξ : UniversalGNS M) : UniversalGNS M :=
  ⟨fun ψ => ψ.gnsStarAlgHom a (ξ ψ), by
    apply ((lp.memℓp ξ).norm.const_smul ‖a‖).mono
    intro ψ
    change ‖ψ.gnsStarAlgHom a (ξ ψ)‖ ≤ ‖a‖ * ‖ξ ψ‖
    exact ((ψ.gnsStarAlgHom a).le_opNorm (ξ ψ)).trans
      (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le ψ.gnsStarAlgHom a)
        (norm_nonneg _))⟩

@[simp] lemma universalGNSAction_apply (a : M) (ξ : UniversalGNS M) (ψ : M →ₚ[ℂ] ℂ) :
    universalGNSAction a ξ ψ = ψ.gnsStarAlgHom a (ξ ψ) := rfl

lemma universalGNSAction_norm (a : M) (ξ : UniversalGNS M) :
    ‖universalGNSAction a ξ‖ ≤ ‖a‖ * ‖ξ‖ := by
  have h : ‖universalGNSAction a ξ‖ ≤ ‖‖a‖ • ξ‖ := by
    apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro ψ
    simp only [universalGNSAction_apply, lp.coeFn_smul, Pi.smul_apply, norm_smul,
      Real.norm_of_nonneg (norm_nonneg a)]
    exact ((ψ.gnsStarAlgHom a).le_opNorm (ξ ψ)).trans
      (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le ψ.gnsStarAlgHom a)
        (norm_nonneg _))
  simpa only [norm_smul, Real.norm_of_nonneg (norm_nonneg a)] using h

def universalGNSOperator (a : M) : UniversalGNS M →L[ℂ] UniversalGNS M :=
  LinearMap.mkContinuous
    { toFun := universalGNSAction a
      map_add' ξ η := by ext ψ; exact map_add (ψ.gnsStarAlgHom a) (ξ ψ) (η ψ)
      map_smul' z ξ := by ext ψ; exact map_smul (ψ.gnsStarAlgHom a) z (ξ ψ) }
    ‖a‖ (universalGNSAction_norm a)

@[simp] lemma universalGNSOperator_apply (a : M) (ξ : UniversalGNS M) (ψ : M →ₚ[ℂ] ℂ) :
    universalGNSOperator a ξ ψ = ψ.gnsStarAlgHom a (ξ ψ) := rfl

def universalGNSRepresentation : M →⋆ₐ[ℂ] (UniversalGNS M →L[ℂ] UniversalGNS M) where
  toFun := universalGNSOperator
  map_zero' := by ext ξ ψ; simp
  map_one' := by ext ξ ψ; simp
  map_add' a b := by ext ξ ψ; simp
  map_mul' a b := by ext ξ ψ; simp
  commutes' z := by
    ext ξ ψ
    exact congrArg (fun A : ψ.GNS →L[ℂ] ψ.GNS => A (ξ ψ)) (ψ.gnsStarAlgHom.commutes z)
  map_star' a := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro ξ η
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    congr 1
    funext ψ
    simp only [universalGNSOperator_apply, map_star]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

@[simp] lemma universalGNSRepresentation_apply (a : M) (ξ : UniversalGNS M)
    (ψ : M →ₚ[ℂ] ℂ) :
    universalGNSRepresentation a ξ ψ = ψ.gnsStarAlgHom a (ξ ψ) := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace
open Classical

namespace BoundedHochschild.KadisonRingrose

open HochschildNormalPart

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def NormalGNS (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) : Type u :=
  normalVectors e (universalGNSRepresentation (M := M))

instance normalGNSNormedAddCommGroup (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    NormedAddCommGroup (NormalGNS e) :=
  inferInstanceAs (NormedAddCommGroup (normalVectors e (universalGNSRepresentation (M := M))))

instance normalGNSInnerProductSpace (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    InnerProductSpace ℂ (NormalGNS e) :=
  inferInstanceAs (InnerProductSpace ℂ (normalVectors e (universalGNSRepresentation (M := M))))

instance normalGNSCompleteSpace (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    CompleteSpace (NormalGNS e) :=
  inferInstanceAs (CompleteSpace (normalVectors e (universalGNSRepresentation (M := M))))

instance normalGNSCoe (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) : CoeOut (NormalGNS e) (UniversalGNS M) :=
  ⟨Subtype.val⟩

def normalGNSOperator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a : M) :
    NormalGNS e →L[ℂ] NormalGNS e :=
  (universalGNSRepresentation a).restrict
    (fun _ξ hξ => normalVectors_mul e universalGNSRepresentation hξ a)

@[simp] lemma normalGNSOperator_coe (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (a : M) (ξ : NormalGNS e) :
    (normalGNSOperator e a ξ : UniversalGNS M) = universalGNSRepresentation a ξ := rfl

lemma normalGNSOperator_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    normalGNSOperator e 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change universalGNSRepresentation (M := M) (0 : M) (ξ : UniversalGNS M) = 0
  simp

lemma normalGNSOperator_one (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    normalGNSOperator e 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change universalGNSRepresentation (M := M) (1 : M) (ξ : UniversalGNS M) = (ξ : UniversalGNS M)
  simp

lemma normalGNSOperator_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M) :
    normalGNSOperator e (a + b) = normalGNSOperator e a + normalGNSOperator e b := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change universalGNSRepresentation (M := M) (a + b) (ξ : UniversalGNS M) =
    universalGNSRepresentation a (ξ : UniversalGNS M) + universalGNSRepresentation b (ξ : UniversalGNS M)
  simp

lemma normalGNSOperator_mul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M) :
    normalGNSOperator e (a * b) = normalGNSOperator e a * normalGNSOperator e b := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change universalGNSRepresentation (M := M) (a * b) (ξ : UniversalGNS M) =
    universalGNSRepresentation a (universalGNSRepresentation b (ξ : UniversalGNS M))
  rw [map_mul]
  rfl

lemma normalGNSOperator_commutes (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (z : ℂ) :
    normalGNSOperator e (algebraMap ℂ M z) = algebraMap ℂ (NormalGNS e →L[ℂ] NormalGNS e) z := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change universalGNSRepresentation (M := M) (algebraMap ℂ M z) (ξ : UniversalGNS M) = z • (ξ : UniversalGNS M)
  exact congrArg (fun A : UniversalGNS M →L[ℂ] UniversalGNS M => A (ξ : UniversalGNS M))
    ((universalGNSRepresentation (M := M)).commutes z)

lemma normalGNSOperator_star (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a : M) :
    normalGNSOperator e (star a) = star (normalGNSOperator e a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  change inner ℂ (universalGNSRepresentation (star a) (ξ : UniversalGNS M)) (η : UniversalGNS M) =
    inner ℂ (ξ : UniversalGNS M) (universalGNSRepresentation a (η : UniversalGNS M))
  rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

def normalGNSRepresentation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    M →⋆ₐ[ℂ] (NormalGNS e →L[ℂ] NormalGNS e) where
  toFun := normalGNSOperator e
  map_zero' := normalGNSOperator_zero e
  map_one' := normalGNSOperator_one e
  map_add' := normalGNSOperator_add e
  map_mul' := normalGNSOperator_mul e
  commutes' := normalGNSOperator_commutes e
  map_star' := normalGNSOperator_star e

@[simp] lemma normalGNSRepresentation_coe (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (a : M) (ξ : NormalGNS e) :
    (normalGNSRepresentation e a ξ : UniversalGNS M) = universalGNSRepresentation a ξ := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable {I H K : Type*} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def representedRightAverage (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (W : H →L[ℂ] K) : H →L[ℂ] K :=
  operatorRowAverage (fun i => π (m i)) (fun i => σ (m i)) W
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology
open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M I H K : Type*} [CStarAlgebra M] [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def weakRepresentedRightAverage (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (W : H →WOT[ℂ] K) : H →WOT[ℂ] K :=
  ContinuousLinearMapWOT.ofCLM (representedRightAverage π σ m W.toCLM)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def representedAveragingOrbit (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) : Set (H →WOT[ℂ] K) :=
  {V | ∃ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) ∧
    V = weakRepresentedRightAverage π σ m W}

def closedRepresentedAveragingOrbit (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) : Set (H →WOT[ℂ] K) :=
  closure (representedAveragingOrbit π σ W)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def RepresentedRightAverageInvariant (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : Set (H →WOT[ℂ] K)) : Prop :=
  ∀ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) →
    Set.MapsTo (weakRepresentedRightAverage π σ m) F F
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def weakCompression (P : K →L[ℂ] K) (Q : H →L[ℂ] H) (W : H →WOT[ℂ] K) :
    H →WOT[ℂ] K :=
  (ContinuousLinearMapWOT.ofCLM P).comp (W.comp (ContinuousLinearMapWOT.ofCLM Q))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def finiteFamilyAverageOrbit {I : Type*} (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) : Set (I → M → WeakDual ℂ X) :=
  {F | ∃ (k : ℕ) (m : Fin k → M), (∑ j, m j * star (m j) = 1) ∧
    F = fun i => weakOperatorImage e (finiteRightAverage m (T i))}

def weakFamilyAverageOrbit {I : Type*} (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) : Set (I → M → WeakDual ℂ X) :=
  closure (finiteFamilyAverageOrbit e T)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

structure MultimodularOver (R : StarSubalgebra ℂ M) {n : ℕ}
    (f : Cochain M (n + 1)) : Prop where
  left : ∀ (r : M), r ∈ R → ∀ x,
    f (Function.update x 0 (r * x 0)) = r * f x
  right : ∀ (r : M), r ∈ R → ∀ x,
    f (Function.update x (Fin.last n) (x (Fin.last n) * r)) = f x * r
  balance : ∀ (r : M), r ∈ R → ∀ x (j : Fin n),
    f (Function.update x j.castSucc (x j.castSucc * r)) =
      f (Function.update x j.succ (r * x j.succ))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

structure MultimodularAt {n : ℕ} (f : Cochain M (n + 1)) (r : M) : Prop where
  left : ∀ x, f (Function.update x 0 (r * x 0)) = r * f x
  right : ∀ x, f (Function.update x (Fin.last n) (x (Fin.last n) * r)) = f x * r
  balance : ∀ x (j : Fin n),
    f (Function.update x j.castSucc (x j.castSucc * r)) =
      f (Function.update x j.succ (r * x j.succ))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners

universe u

def ProperlyInfiniteVanishingInput : Prop :=
  ∀ (N : Type u) [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N],
    WStarAlgebra N → NoFiniteCentralSummand N →
    ∀ (n : ℕ) (f : Cochain N (n + 2)), (∀ x, differentialValue f x = 0) →
      ∃ g : Cochain N (n + 1), ∀ x, differentialValue g x = f x
end BoundedHochschild.KadisonRingrose
end
end OAI
end


