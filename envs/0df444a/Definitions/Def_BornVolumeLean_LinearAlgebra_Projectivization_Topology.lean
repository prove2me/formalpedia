-- Prove2me | Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Topology
-- name    : BornVolumeLean_LinearAlgebra_Projectivization_Topology
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:31.889143+00:00
-- url     : https://prove2.me/theorems/e0b2f5c4-d416-4979-a15e-f05f6fe44715
-- title:
--   Topology
-- statement:
--   Definitions and structural lemmas for Topology, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/Topology.lean

module
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Definitions.Def_BornVolumeLean_Topology_Algebra_MulAction
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Topology.Separation.Hausdorff
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set Function Topology
open scoped LinearAlgebra.Projectivization
namespace Projectivization
variable {K V : Type*}
section AlgebraicTopology
variable [DivisionRing K] [AddCommGroup V] [Module K V]
section
theorem mk'_eq_mk'_iff_staged (v w : {v : V // v ≠ 0}) :
    mk' K v = mk' K w ↔ ∃ a : Kˣ, a • w = v := by
  rw [mk'_eq_mk, mk'_eq_mk, mk_eq_mk_iff]
  simp only [Subtype.ext_iff, Units.smul_coe]
theorem preimage_image_mk'_staged (U : Set {v : V // v ≠ 0}) :
    mk' K ⁻¹' (mk' K '' U) = ⋃ a : Kˣ, (a • ·) '' U := by
  ext v
  simp only [mem_preimage, mem_image, mk'_eq_mk'_iff_staged, mem_iUnion]
  exact ⟨fun ⟨w, hw, a, h⟩ ↦ ⟨a⁻¹, w, hw, by rw [← h, inv_smul_smul]⟩,
    fun ⟨a, w, hw, h⟩ ↦ ⟨w, hw, a⁻¹, by rw [← h, inv_smul_smul]⟩⟩
variable [TopologicalSpace V]
instance instTopologicalSpace : TopologicalSpace (ℙ K V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid K V)))
theorem isQuotientMap_mk' : IsQuotientMap (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  isQuotientMap_quotient_mk'
@[continuity, fun_prop]
theorem continuous_mk' : Continuous (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  continuous_quotient_mk'
variable {α : Type*} [TopologicalSpace α]
variable [ContinuousConstSMul Kˣ V]
theorem isOpenMap_mk' : IsOpenMap (mk' K : {v : V // v ≠ 0} → ℙ K V) := fun U hU ↦ by
  rw [← isQuotientMap_mk'.isCoinducing.isOpen_preimage, preimage_image_mk'_staged]
  exact isOpen_iUnion fun a ↦ isOpenMap_smul a U hU
theorem isOpenQuotientMap_mk' : IsOpenQuotientMap (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  ⟨Quotient.mk''_surjective, continuous_mk', isOpenMap_mk'⟩
end
section MapContinuity
variable [TopologicalSpace V]
variable {W : Type*} [AddCommGroup W] [Module K W] [TopologicalSpace W]
end MapContinuity
section LinearEquivAction
def mapEquiv (e : V ≃ₗ[K] V) : ℙ K V → ℙ K V :=
  Projectivization.map e.toLinearMap e.injective
variable [TopologicalSpace V]
end LinearEquivAction
end AlgebraicTopology
section NormedFiniteDim
variable [RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]
omit [FiniteDimensional K V] in
/-- The K-collinearity relation on the nonzero subtype is closed.

Two nonzero vectors `v, w` represent the same projective point iff their
pair is linearly dependent (`mk_eq_mk_iff'` + `LinearIndependent.pair_iff'`),
and the set of linearly dependent pairs is the complement of an open set
via `isOpen_setOfPred_linearIndependent`. -/
lemma isClosed_collinearity_relation :
    IsClosed { p : { v : V // v ≠ 0 } × { v : V // v ≠ 0 } |
                mk' K p.1 = mk' K p.2 } := by
  -- Map `(v_sub, w_sub) ↦ ![w, v] : Fin 2 → V`. The collinearity set is
  -- the preimage of `¬ LinearIndependent K`-pairs, which is the
  -- complement of `isOpen_setOfPred_linearIndependent`.
  let f : { v : V // v ≠ 0 } × { v : V // v ≠ 0 } → (Fin 2 → V) :=
    fun p => ![(p.2 : V), (p.1 : V)]
  have hf : Continuous f := by
    refine continuous_pi (fun i => ?_)
    fin_cases i
    · exact continuous_subtype_val.comp continuous_snd
    · exact continuous_subtype_val.comp continuous_fst
  have h_eq : { p : { v : V // v ≠ 0 } × { v : V // v ≠ 0 } |
                  mk' K p.1 = mk' K p.2 }
            = f ⁻¹' { g : Fin 2 → V | LinearIndependent K g }ᶜ := by
    ext ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, f]
    rw [mk'_eq_mk, mk'_eq_mk, mk_eq_mk_iff' K v w hv hw,
        LinearIndependent.pair_iff' hw]
    push Not
    rfl
  rw [h_eq]
  exact isOpen_setOfPred_linearIndependent.isClosed_compl.preimage hf
instance instT2Space : T2Space (ℙ K V) :=
  (t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_mk').mpr
    isClosed_collinearity_relation
instance instCompactSpace : CompactSpace (ℙ K V) := by
  have : ProperSpace V := FiniteDimensional.proper_rclike K V
  -- Define the corestricted projection sphere → ℙ K V.
  let g : Metric.sphere (0 : V) 1 → ℙ K V :=
    fun v => mk K (v : V) (by
      intro hv
      have h1 : ‖(v : V)‖ = 1 := by
        have := v.2; rwa [Metric.mem_sphere, dist_zero_right] at this
      rw [hv, norm_zero] at h1
      exact one_ne_zero h1.symm)
  have hg_cont : Continuous g :=
    continuous_quotient_mk'.comp (continuous_induced_rng.mpr continuous_subtype_val)
  have hg_surj : Function.Surjective g := by
    intro p
    have hrep_ne : p.rep ≠ 0 := p.rep_nonzero
    have hrep_norm_pos : 0 < ‖p.rep‖ := norm_pos_iff.mpr hrep_ne
    have h_norm_eq : ‖((‖p.rep‖⁻¹ : ℝ) : K) • p.rep‖ = 1 := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hrep_norm_pos)]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hrep_ne)
    have h_sphere : ((‖p.rep‖⁻¹ : ℝ) : K) • p.rep ∈ Metric.sphere (0 : V) 1 :=
      mem_sphere_zero_iff_norm.mpr h_norm_eq
    refine ⟨⟨((‖p.rep‖⁻¹ : ℝ) : K) • p.rep, h_sphere⟩, ?_⟩
    -- `g ⟨smul_vec, h_sphere⟩ = p` via `mk_eq_mk_iff'` and `mk_rep`.
    show mk K (((‖p.rep‖⁻¹ : ℝ) : K) • p.rep) _ = p
    conv_rhs => rw [← p.mk_rep]
    rw [mk_eq_mk_iff' K _ _ _ hrep_ne]
    exact ⟨((‖p.rep‖⁻¹ : ℝ) : K), rfl⟩
  exact ⟨hg_surj.range_eq ▸ isCompact_range hg_cont⟩
end NormedFiniteDim
end Projectivization


