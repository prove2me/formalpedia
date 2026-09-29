-- Prove2me | solution 1 for AutomorphicForm.adelicKernelLocalFiniteness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5cb232fa-9c6c-5a29-9a79-f6d5e88b6e50

import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_adelicKernelLocalFiniteness

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicBox
open scoped Pointwise

noncomputable section

namespace M4aP3B
namespace Rows
namespace Discrete

variable (F : Type) [Field F] [NumberField F]

theorem fst_algebraMap (ξ : F) :
    (algebraMap F (AdeleRing (𝓞 F) F) ξ).1 = algebraMap F (InfiniteAdeleRing F) ξ := rfl

theorem zero_mem_integralFiniteAdeles' :
    (0 : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun _ => zero_mem _

theorem finite_setOf_algebraMap_mem {C : Set (AdeleRing (𝓞 F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C}.Finite := by
  classical

  have hO : IsOpen (integralFiniteAdeles (𝓞 F) F) := isOpen_integralFiniteAdeles F
  have hCf : IsCompact (Prod.snd '' C) := hC.image continuous_snd
  obtain ⟨t, -, hcover⟩ := hCf.elim_nhds_subcover
    (fun y => (fun z => z - y) ⁻¹' integralFiniteAdeles (𝓞 F) F) fun y _ =>
      (hO.preimage (continuous_id.sub continuous_const)).mem_nhds
        (by simpa only [Set.mem_preimage, Pi.sub_apply, id_eq, sub_self] using zero_mem_integralFiniteAdeles' F)

  have hCinf : IsCompact (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) :=
    (hC.image continuous_fst).image (continuous_ringEquiv_mixedSpace F)
  have hD : IsCompact ((fun p : mixedEmbedding.mixedSpace F × mixedEmbedding.mixedSpace F =>
      p.1 - p.2) '' ((InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) ×ˢ
        (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)))) :=
    (hCinf.prod hCinf).image (continuous_fst.sub continuous_snd)

  haveI : DiscreteTopology (mixedEmbedding.integerLattice F).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (mixedEmbedding.integerLattice F))
  have hL : ((fun p : mixedEmbedding.mixedSpace F × mixedEmbedding.mixedSpace F => p.1 - p.2) ''
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) ×ˢ
        (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C))) ∩
      (mixedEmbedding.integerLattice F : Set (mixedEmbedding.mixedSpace F))).Finite := by
    refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hD.isBounded ?_
    rw [← Submodule.coe_toAddSubgroup]
    exact AddSubgroup.isClosed_of_discrete

  have hT : ∀ y : FiniteAdeleRing (𝓞 F) F,
      {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C ∧
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - y ∈ integralFiniteAdeles (𝓞 F) F}.Finite := by
    intro y
    rcases Set.eq_empty_or_nonempty {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C ∧
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - y ∈ integralFiniteAdeles (𝓞 F) F} with h0 | ⟨ξ₀, hξ₀C, hξ₀y⟩
    · rw [h0]; exact Set.finite_empty
    refine (hL.preimage (f := fun ξ : F => mixedEmbedding F (ξ - ξ₀)) fun a _ b _ h =>
      sub_left_inj.1 (mixedEmbedding_injective F h)).subset ?_
    rintro ξ ⟨hξC, hξy⟩
    refine ⟨?_, ?_⟩
    ·
      refine ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ).1,
          InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1),
        ⟨⟨(algebraMap F (AdeleRing (𝓞 F) F) ξ).1, ⟨_, hξC, rfl⟩, rfl⟩,
          ⟨(algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1, ⟨_, hξ₀C, rfl⟩, rfl⟩⟩, ?_⟩
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ).1
          - InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1
        = mixedEmbedding F (ξ - ξ₀)
      rw [map_sub, fst_algebraMap, fst_algebraMap, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
        ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    ·
      have h2 : (algebraMap F (AdeleRing (𝓞 F) F) (ξ - ξ₀)).2
          = (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).2 := by
        rw [map_sub]; rfl
      have hdiff : (algebraMap F (AdeleRing (𝓞 F) F) (ξ - ξ₀)).2 ∈ integralFiniteAdeles (𝓞 F) F := by
        rw [h2, ← sub_sub_sub_cancel_right _ _ y]
        exact fun v => sub_mem (hξy v) (hξ₀y v)
      have hval : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ - ξ₀) ≤ 1 := fun v => by
        have h := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hdiff v)
        rwa [NumberField.AdeleRing.algebraMap_snd_apply,
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
      obtain ⟨o, ho⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (ξ - ξ₀) hval
      show mixedEmbedding F (ξ - ξ₀) ∈ (mixedEmbedding.integerLattice F : Set (mixedEmbedding.mixedSpace F))
      rw [← ho]
      exact ⟨o, rfl⟩

  refine (t.finite_toSet.biUnion fun y _ => hT y).subset fun ξ hξ => ?_
  have h2 : (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 ∈ Prod.snd '' C := ⟨_, hξ, rfl⟩
  obtain ⟨y, hy, hyO⟩ := Set.mem_iUnion₂.1 (hcover h2)
  exact Set.mem_iUnion₂.2 ⟨y, hy, hξ, hyO⟩

theorem globalPoints_entry (γ : GL (Fin 2) F) (i j : Fin 2) :
    ((globalPoints (𝓞 F) F γ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      = algebraMap F (AdeleRing (𝓞 F) F) ((γ : Matrix (Fin 2) (Fin 2) F) i j) := rfl

theorem adelicKernelLocalFiniteness_impl : AdelicKernelLocalFiniteness F := by
  intro C hC x y

  have hC' : IsCompact ((fun g : AdelicGL2 (𝓞 F) F => x * g * y⁻¹) '' C) :=
    hC.image ((continuous_const.mul continuous_id).mul continuous_const)

  have hE : ∀ i j : Fin 2, IsCompact ((fun g : AdelicGL2 (𝓞 F) F =>
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) ''
        ((fun g : AdelicGL2 (𝓞 F) F => x * g * y⁻¹) '' C)) :=
    fun i j => hC'.image (Units.continuous_val.matrix_elem i j)

  have hA : ∀ i j : Fin 2, {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈
      (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) ''
        ((fun g : AdelicGL2 (𝓞 F) F => x * g * y⁻¹) '' C)}.Finite :=
    fun i j => finite_setOf_algebraMap_mem F (hE i j)
  have hfin : {m : Fin 2 → Fin 2 → F | ∀ i, m i ∈ {r : Fin 2 → F | ∀ j, r j ∈
      {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈
        (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) ''
          ((fun g : AdelicGL2 (𝓞 F) F => x * g * y⁻¹) '' C)}}}.Finite :=
    Set.Finite.pi' fun i => Set.Finite.pi' fun j => hA i j
  refine (hfin.preimage (f := (Units.val : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F))
    Units.val_injective.injOn).subset fun γ hγ => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  intro i j
  exact ⟨globalPoints (𝓞 F) F γ, ⟨x⁻¹ * globalPoints (𝓞 F) F γ * y, hγ, by simp [mul_assoc]⟩, rfl⟩

theorem gate_empty (x y : AdelicGL2 (𝓞 F) F) :
    {γ : GL (Fin 2) F | x⁻¹ * globalPoints (𝓞 F) F γ * y ∈ (∅ : Set (AdelicGL2 (𝓞 F) F))}.Finite := by
  simp

theorem gate_one_mem (C : Set (AdelicGL2 (𝓞 F) F)) (x y : AdelicGL2 (𝓞 F) F) (h : x⁻¹ * y ∈ C) :
    (1 : GL (Fin 2) F) ∈ {γ : GL (Fin 2) F | x⁻¹ * globalPoints (𝓞 F) F γ * y ∈ C} := by
  simpa using h

end M4aP3B.Rows.Discrete

end

#print axioms M4aP3B.Rows.Discrete.adelicKernelLocalFiniteness_impl
#print axioms M4aP3B.Rows.Discrete.finite_setOf_algebraMap_mem

theorem solution (F : Type) [Field F] [NumberField F] :
    AutomorphicForm.AdelicKernelLocalFiniteness F := by
  exact M4aP3B.Rows.Discrete.adelicKernelLocalFiniteness_impl F

end S_AutomorphicForm_adelicKernelLocalFiniteness
end P2MW
export P2MW.S_AutomorphicForm_adelicKernelLocalFiniteness (solution)
