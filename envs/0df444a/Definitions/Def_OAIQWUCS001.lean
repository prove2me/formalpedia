-- Prove2me | Definitions.Def_OAIQWUCS001
-- name    : OAIQWUCS001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T00:47:37.161961+00:00
-- url     : https://prove2.me/theorems/3eadc81f-ba2d-4d09-9219-de50ce5d05e1
-- title:
--   Commuting holomorphic flows and involutive projection fields (OpenAI universal-cover splitting)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniversalCoverSplitting.main`. Its definitions are the ones the proof of the holomorphic Frobenius theorem (the standalone statement `OAI.UniversalCoverSplitting.holomorphic_frobenius_theorem`) works with.
--
--   The bundle holds OpenAI's Lean definitions from the modules `CommutingFlows` and `Frobenius` of `lean/OAI/Geometry/KahlerSplitting` (OpenAI, *Universal-cover splitting for compact Kähler manifolds*, OpenAI Math Release, September 23, 2026, result family 052, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas their bodies use. Among them:
--   - multi-times $\mathbb C^n$ (`FlowTimes`, `trimFlowTimes`) and OpenAI's structure `CommutingFlowData`: the joint local flow of $n$ commuting holomorphic vector fields, with its properties as fields;
--   - OpenAI's predicate `InvolutiveProjectionOn P U`: the image distribution of a field of projections $P$ is closed under the Lie bracket of holomorphic vector fields tangent to it. The standalone Frobenius statement writes this hypothesis out in full;
--   - a radial clamp onto a ball (`radialClamp`), and the transverse parameter and its linear part (`transverseFlowParameter`, `transverseFlowLinear`) that place the flows' starting points on a complementary slice;
--   - holomorphic inverse-function charts and projection coordinates (`exists_holomorphic_ift_chart`, `exists_projection_coordinates`).
--
--   The theorems the definitions do not need are proved in the solutions of this split.
-- source:
--   OpenAI, Universal-cover splitting for compact Kähler manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/KahlerSplitting at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_UniversalCover.CommutingFlows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

abbrev FlowTimes (n : ℕ) := Fin n → ℂ

def trimFlowTimes (n : ℕ) : FlowTimes (n+1) →L[ℂ] FlowTimes n :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj i.castSucc)

@[simp] theorem trimFlowTimes_apply (n : ℕ) (t : FlowTimes (n+1)) (i : Fin n) :
    trimFlowTimes n t i = t i.castSucc := rfl

@[simp] theorem trimFlowTimes_single_castSucc (n : ℕ) (i : Fin n) :
    trimFlowTimes n (Pi.single i.castSucc (1 : ℂ)) = Pi.single i 1 := by
  ext j
  simp [Pi.single_apply]

@[simp] theorem trimFlowTimes_single_last (n : ℕ) :
    trimFlowTimes n (Pi.single (Fin.last n) (1 : ℂ)) = 0 := by
  ext j
  simp

structure CommutingFlowData (n : ℕ) (V : Fin n → C(E,E))
    (D : Fin n → C(E,E →L[ℂ] E)) (U : Set E) (p : E) where
  domain : Set (E × FlowTimes n)
  isOpen_domain : IsOpen domain
  base_mem : (p,0) ∈ domain
  map : E × FlowTimes n → E
  contDiff : ContDiffOn ℂ 1 map domain
  mapsTo : MapsTo map domain U
  zero : ∀ x, (x,0) ∈ domain → map (x,0) = x
  time : ∀ q ∈ domain, ∀ i : Fin n,
    fderiv ℂ map q (0,Pi.single i 1) = V i (map q)
  preserves : ∀ (A : C(E,E)) (DA : E → E →L[ℂ] E),
    (∀ x ∈ U, HasFDerivAt A (DA x) x) →
    (∀ i x, x ∈ U → DA x (V i x) = D i x (A x)) →
    ∀ q ∈ domain, fderiv ℂ map q (A q.1,0) = A (map q)

end UniversalCoverSplitting

open Set Filter Topology Metric Complex
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem continuousOn_directional_cauchy {U S : Set E} {f : E → F}
    (hf : ContinuousOn f U) (e : E) {r : ℝ} (hr : 0 < r)
    (hmap : ∀ z ∈ S, ∀ θ : ℝ, z + circleMap 0 r θ • e ∈ U) :
    ContinuousOn (fun z ↦ cderiv r (fun w : ℂ ↦ f (z + w • e)) 0) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  let G : S → ℝ → F := fun z θ ↦
    (circleMap 0 r θ * I) • (((circleMap 0 r θ)^2)⁻¹ •
      f (z.val + circleMap 0 r θ • e))
  have hG : Continuous G.uncurry := by
    have hc : Continuous (fun p : S × ℝ ↦ p.1.val + circleMap 0 r p.2 • e) := by
      fun_prop
    have hm : MapsTo (fun p : S × ℝ ↦ p.1.val + circleMap 0 r p.2 • e) univ U :=
      fun p _ ↦ hmap p.1.val p.1.property p.2
    have hcomp := continuousOn_univ.mp (hf.comp hc.continuousOn hm)
    have hne (p : S × ℝ) : circleMap 0 r p.2 ≠ 0 :=
      circleMap_ne_mem_ball (mem_ball_self hr) p.2
    dsimp [G, Function.uncurry]
    apply Continuous.smul
    · fun_prop
    · exact (((continuous_circleMap 0 r).comp continuous_snd).pow 2).inv₀
        (fun p ↦ pow_ne_zero 2 (hne p)) |>.smul hcomp
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) hG (a₀ := 0) (b₀ := 2 * Real.pi)
  convert! hi.const_smul ((2 * Real.pi * I : ℂ)⁻¹) using 1
  ext z
  simp only [cderiv, circleIntegral, deriv_circleMap, G, circleMap, zero_add,
    sub_zero, Pi.smul_apply, Set.domRestrict]

variable [CompleteSpace F]

theorem continuousAt_directional_fderiv {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) {p : E} (hp : p ∈ U) (e : E) :
    ContinuousAt (fun z ↦ fderiv ℂ f z e) p := by
  obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let r : ℝ := d / (2 * (‖e‖ + 1))
  have he : 0 < ‖e‖ + 1 := by positivity
  have hr : 0 < r := div_pos hd (by positivity)
  have hre : r * ‖e‖ ≤ d / 2 := by
    have hprod : r * (‖e‖ + 1) = d / 2 := by
      dsimp [r]; field_simp
    nlinarith
  let S := ball p (d / 2)
  have hS : S ∈ 𝓝 p := ball_mem_nhds _ (by linarith)
  have hmap (z : E) (hz : z ∈ S) (w : ℂ) (hw : w ∈ closedBall 0 r) :
      z + w • e ∈ U := by
    apply hdU
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    calc
      ‖z + w • e - p‖ = ‖(z-p) + w • e‖ := by congr 1; abel
      _ ≤ ‖z-p‖ + ‖w • e‖ := norm_add_le _ _
      _ = ‖z-p‖ + ‖w‖ * ‖e‖ := by rw [norm_smul]
      _ ≤ ‖z-p‖ + r * ‖e‖ := by gcongr
      _ < d := by linarith
  have hc := continuousOn_directional_cauchy hf.continuousOn e hr
    (fun z hz θ ↦ hmap z hz _ (circleMap_mem_closedBall _ hr.le _))
  have heq : (fun z ↦ cderiv r (fun w : ℂ ↦ f (z + w • e)) 0)
      =ᶠ[𝓝 p] (fun z ↦ fderiv ℂ f z e) := by
    filter_upwards [hS] with z hz
    let V : Set ℂ := (fun w : ℂ ↦ z + w • e) ⁻¹' U
    have hV : IsOpen V := hU.preimage (by fun_prop)
    have hline : DifferentiableOn ℂ (fun w : ℂ ↦ f (z + w • e)) V :=
      hf.comp (by fun_prop) (fun _ hw ↦ hw)
    rw [cderiv_eq_deriv hV hline hr (hmap z hz)]
    have hzU : z ∈ U := by simpa using hmap z hz 0 (mem_closedBall_self hr.le)
    have hdline : HasDerivAt (fun w : ℂ ↦ z + w • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add z
    have hdf := (hf.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt
    have hh := (show HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • e) by
      simpa using hdf).comp_hasDerivAt 0 hdline
    simpa only [Function.comp_def] using hh.deriv
  exact (hc.continuousAt hS).congr heq

end UniversalCoverSplitting

open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialClamp (p : E) (r : ℝ) (x : E) : E :=
  p + (r / max r ‖x-p‖) • (x-p)

end UniversalCoverSplitting
open Set Metric Filter Topology

open Set Metric Filter Topology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Frobenius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Metric Filter Topology
open Set Filter Topology Metric
open scoped ContDiff

open Set Filter Topology

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def InvolutiveProjectionOn (P : E → E →L[ℂ] E) (U : Set E) : Prop :=
  ∀ V W : E → E, DifferentiableOn ℂ V U → DifferentiableOn ℂ W U →
    (∀ x ∈ U, P x (V x) = V x) → (∀ x ∈ U, P x (W x) = W x) →
    ∀ x ∈ U, P x (VectorField.lieBracket ℂ V W x) = VectorField.lieBracket ℂ V W x

end UniversalCoverSplitting

open Set Filter Topology

open Set Metric Filter Topology
open scoped ContDiff

open Set Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup C] [NormedSpace ℂ C]

abbrev transverseFlowParameter {n : ℕ} (p : E) (L : (FlowTimes n × C) ≃L[ℂ] E)
    (q : FlowTimes n × C) : E × FlowTimes n := (p+L (0,q.2),q.1)

def transverseFlowLinear {n : ℕ} (L : (FlowTimes n × C) ≃L[ℂ] E) :
    (FlowTimes n × C) →L[ℂ] E × FlowTimes n :=
  ((L : (FlowTimes n × C) →L[ℂ] E).comp
    ((0 : (FlowTimes n × C) →L[ℂ] FlowTimes n).prod (ContinuousLinearMap.snd ℂ _ _))).prod
    (ContinuousLinearMap.fst ℂ _ _)

end UniversalCoverSplitting

open Set Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_holomorphic_ift_chart {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : ContDiffOn ℂ 1 f U) {p : E} (hp : p ∈ U)
    (L : E ≃L[ℂ] F) (hL : HasFDerivAt f (L : E →L[ℂ] F) p) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ p ∈ e.source ∧
      e.source ⊆ U ∧ ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target := by
  have hc := hf.contDiffAt (hU.mem_nhds hp)
  have hn : (1 : ℕ∞ω) ≠ 0 := by norm_num
  let e := hc.toOpenPartialHomeomorph f hL hn
  have hpe : p ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hL hn
  have hi : ContDiffAt ℂ 1 e.symm (f p) := hc.to_localInverse hL hn
  obtain ⟨R,hR,hRi⟩ := hi.contDiffOn le_rfl (by norm_num)
  obtain ⟨O,hOR,hOo,hOp⟩ := _root_.mem_nhds_iff.mp hR
  let S := U ∩ f ⁻¹' O
  have hS : IsOpen S := hf.continuousOn.isOpen_inter_preimage hU hOo
  let g := e.restrOpen S hS
  have hgf : (g : E → F) = f := rfl
  have hGU : g.source ⊆ U := fun x hx ↦ hx.2.1
  refine ⟨g,hgf,⟨hpe,hp,hOp⟩,hGU,?_,?_⟩
  · rw [hgf]
    exact hf.mono hGU
  · intro y hy
    have hx := g.map_target hy
    have hfy : f (g.symm y) = y := g.right_inv hy
    have hyO : y ∈ O := hfy ▸ hx.2.2
    exact (hRi y (hOR hyO)).mono (fun z hz ↦ by
      have hz' := g.map_target hz
      have heq : f (g.symm z) = z := g.right_inv hz
      exact hOR (heq ▸ hz'.2.2))

end UniversalCoverSplitting

open Set Filter Topology

open Set Filter Topology
open scoped ContDiff

open Set

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_projection_coordinates (P : E →L[ℂ] E)
    (hid : ∀ v, P (P v) = P v) {r s : ℕ}
    (hr : Module.finrank ℂ (LinearMap.range P.toLinearMap) = r)
    (hs : Module.finrank ℂ (LinearMap.ker P.toLinearMap) = s) :
    ∃ L : ((Fin r → ℂ) × (Fin s → ℂ)) ≃L[ℂ] E,
      ∀ v, L ((L.symm v).1,0) = P v := by
  have hP : IsIdempotentElem P.toLinearMap := by
    ext v
    exact hid v
  let R := LinearMap.range P.toLinearMap
  let K := LinearMap.ker P.toLinearMap
  let a : R ≃ₗ[ℂ] (Fin r → ℂ) := (Module.finBasisOfFinrankEq ℂ R hr).equivFun
  let b : K ≃ₗ[ℂ] (Fin s → ℂ) := (Module.finBasisOfFinrankEq ℂ K hs).equivFun
  let e : (R × K) ≃ₗ[ℂ] E := Submodule.prodEquivOfIsCompl R K (LinearMap.IsIdempotentElem.isCompl hP)
  let L := ((a.symm.prodCongr b.symm).trans e).toContinuousLinearEquiv
  refine ⟨L,?_⟩
  intro v
  obtain ⟨q,rfl⟩ := L.surjective v
  rw [L.symm_apply_apply]
  have hR : P (a.symm q.1) = a.symm q.1 := (LinearMap.IsIdempotentElem.mem_range_iff hP).mp (a.symm q.1).property
  have hK : P (b.symm q.2) = 0 := (b.symm q.2).property
  change ((a.symm q.1 : R) : E) + ((b.symm 0 : K) : E) =
    P (((a.symm q.1 : R) : E) + ((b.symm q.2 : K) : E))
  simp only [map_zero,Submodule.coe_zero,map_add,hR,hK,add_zero]

end UniversalCoverSplitting

end

end OAI
end


