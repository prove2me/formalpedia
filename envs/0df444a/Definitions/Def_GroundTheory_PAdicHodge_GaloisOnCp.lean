-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
-- name    : GroundTheory_PAdicHodge_GaloisOnCp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:35.75368+00:00
-- url     : https://prove2.me/theorems/e1ec659c-d24e-4899-9a6c-5a20ee220d6d
-- title:
--   Galois On Cp
-- statement:
--   Definitions and structural lemmas for Galois On Cp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/GaloisOnCp.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open UniformSpace Topology Filter
noncomputable section
theorem continuousSMul_of_isometry_of_dense {G X : Type*} [Monoid G] [TopologicalSpace G]
    [PseudoMetricSpace X] [MulAction G X] (D : Set X) (hD : Dense D)
    (hiso : ∀ g : G, Isometry fun x : X => g • x)
    (horb : ∀ d ∈ D, Continuous fun g : G => g • d) : ContinuousSMul G X := by
  refine ⟨continuous_iff_continuousAt.2 fun ⟨g₀, x₀⟩ => ?_⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨d, hd, hxd⟩ := Metric.mem_closure_iff.1 (hD x₀) (ε / 4) (by positivity)
  have h1 : ∀ᶠ g in 𝓝 g₀, dist (g • d) (g₀ • d) < ε / 4 :=
    Metric.tendsto_nhds.1 ((horb d hd).tendsto g₀) _ (by positivity)
  have h2 : ∀ᶠ x in 𝓝 x₀, dist x x₀ < ε / 4 := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [h1.prod_nhds h2] with q hq
  obtain ⟨hg, hx⟩ := hq
  have e1 : dist (q.1 • q.2) (q.1 • d) = dist q.2 d := (hiso q.1).dist_eq q.2 d
  have e2 : dist (g₀ • d) (g₀ • x₀) = dist d x₀ := (hiso g₀).dist_eq d x₀
  have e3 : dist q.2 d ≤ dist q.2 x₀ + dist x₀ d := dist_triangle _ _ _
  have e4 : dist d x₀ = dist x₀ d := dist_comm _ _
  calc dist (q.1 • q.2) (g₀ • x₀)
      ≤ dist (q.1 • q.2) (q.1 • d) + dist (q.1 • d) (g₀ • d) + dist (g₀ • d) (g₀ • x₀) :=
        dist_triangle4 _ _ _ _
    _ < ε := by rw [e1, e2, e4]; linarith
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
theorem spectralNorm_gal_apply (σ : Gal(PadicAlgCl p/K)) (x : PadicAlgCl p) :
    spectralNorm ℚ_[p] (PadicAlgCl p) (σ x) = spectralNorm ℚ_[p] (PadicAlgCl p) x :=
  (spectralNorm_eq_of_equiv (σ.restrictScalars ℚ_[p]) x).symm
theorem norm_gal_apply (σ : Gal(PadicAlgCl p/K)) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ :=
  spectralNorm_gal_apply σ x
theorem isometry_gal (σ : Gal(PadicAlgCl p/K)) : Isometry σ :=
  AddMonoidHomClass.isometry_of_norm σ (norm_gal_apply σ)
instance : UniformContinuousConstSMul Gal(PadicAlgCl p/K) (PadicAlgCl p) :=
  ⟨fun σ => (isometry_gal σ).uniformContinuous⟩
instance : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top ℚ_[p]
theorem continuous_gal_apply (y : PadicAlgCl p) :
    Continuous fun σ : Gal(PadicAlgCl p/K) => σ • y := by
  refine continuous_iff_continuousAt.2 fun σ₀ => tendsto_nhds_of_eventually_eq ?_
  let S := MulAction.stabilizer Gal(PadicAlgCl p/K) y
  have hS : (S : Set Gal(PadicAlgCl p/K)) ∈ 𝓝 (σ₀⁻¹ * σ₀) := by
    rw [inv_mul_cancel]
    exact (stabilizer_isOpen_of_isIntegral y).mem_nhds S.one_mem
  filter_upwards [(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds hS]
    with σ hσ
  have h : (σ₀⁻¹ * σ) • y = y := hσ
  rw [mul_smul, inv_smul_eq_iff] at h
  exact h
instance : ContinuousSMul Gal(PadicAlgCl p/K) (PadicAlgCl p) :=
  continuousSMul_of_isometry_of_dense Set.univ dense_univ (fun σ => isometry_gal σ)
    (fun y _ => continuous_gal_apply y)
theorem gal_smul_coe (σ : Gal(PadicAlgCl p/K)) (y : PadicAlgCl p) :
    σ • (y : ℂ_[p]) = ((σ y : PadicAlgCl p) : ℂ_[p]) :=
  (Completion.coe_smul σ y).symm
instance instMulSemiringActionCp : MulSemiringAction Gal(PadicAlgCl p/K) ℂ_[p] :=
  { (inferInstance : DistribMulAction Gal(PadicAlgCl p/K) ℂ_[p]) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, gal_smul_coe, map_one]
    smul_mul := fun σ x y => by
      refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) fun a b => ?_
      · exact (continuous_const_smul σ).comp (continuous_fst.mul continuous_snd)
      · exact ((continuous_const_smul σ).comp continuous_fst).mul
          ((continuous_const_smul σ).comp continuous_snd)
      · rw [← Completion.coe_mul, gal_smul_coe, gal_smul_coe, gal_smul_coe, map_mul,
          Completion.coe_mul] }
theorem norm_smul_gal (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) : ‖σ • x‖ = ‖x‖ := by
  refine Completion.induction_on x
    (isClosed_eq (continuous_norm.comp (continuous_const_smul σ)) continuous_norm) fun a => ?_
  rw [gal_smul_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_gal_apply]
theorem isometry_smul_gal (σ : Gal(PadicAlgCl p/K)) : Isometry fun x : ℂ_[p] => σ • x :=
  Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul_gal]
instance : ContinuousSMul Gal(PadicAlgCl p/K) ℂ_[p] :=
  continuousSMul_of_isometry_of_dense (Set.range ((↑) : PadicAlgCl p → ℂ_[p]))
    Completion.denseRange_coe isometry_smul_gal (by
      rintro _ ⟨y, rfl⟩
      simp_rw [gal_smul_coe]
      exact (Completion.continuous_coe _).comp (continuous_gal_apply y))
instance : FaithfulSMul Gal(PadicAlgCl p/K) ℂ_[p] :=
  ⟨fun h => AlgEquiv.ext fun y => Completion.coe_injective (PadicAlgCl p) <| by
    rw [← gal_smul_coe, ← gal_smul_coe, h]⟩
def galCp (σ : Gal(PadicAlgCl p/K)) : ℂ_[p] ≃+* ℂ_[p] :=
  MulSemiringAction.toRingEquiv _ ℂ_[p] σ
def galCpHom : Gal(PadicAlgCl p/K) →* RingAut ℂ_[p] :=
  MulSemiringAction.toRingAut _ ℂ_[p]
end
end GroundTheory.PAdicHodge


