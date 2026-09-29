-- Prove2me | solution 1 for AutomorphicForm.exists_finset_adelicMaximalCompact_finiteAdelic_coset_principalLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ae2974f6-e657-5596-9ab4-9b15f4b48794

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_adelicMaximalCompact_finiteAdelic_coset_principalLevel

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    ∃ (n : ℕ) (r : Fin n → AdelicGL2 (𝓞 K) K),
      (∀ i, r i ∈ adelicMaximalCompact K ∧ r i ∈ finiteAdelicGL2Subgroup K) ∧
      ∀ k ∈ adelicMaximalCompact K, k ∈ finiteAdelicGL2Subgroup K →
        ∃ i, (r i)⁻¹ * k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  classical
  set S : Set (AdelicGL2 (𝓞 K) K) :=
    (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) ∩ (finiteAdelicGL2Subgroup K : Set (AdelicGL2 (𝓞 K) K))
    with hS
  have hSc : IsCompact S := (isCompact_adelicMaximalCompact K).inter_right (isClosed_finiteAdelicGL2Subgroup K)
  set P : Set (AdelicGL2 (𝓞 K) K) := (principalLevel (𝓞 K) K N : Set (AdelicGL2 (𝓞 K) K)) with hP

  have hPo : IsOpen P := by
    have h1 : IsOpen (levelOne (𝓞 K) K N : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) := isOpen_levelOne (𝓞 K) K hN
    have h2 : IsOpen (((levelOne (𝓞 K) K N).map (MulAut.conj (weyl (𝓞 K) K)).toMonoidHom :
        Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) := by
      rw [Subgroup.coe_map]
      let e : GL (Fin 2) (AdeleRing (𝓞 K) K) ≃ₜ GL (Fin 2) (AdeleRing (𝓞 K) K) :=
        (Homeomorph.mulLeft (weyl (𝓞 K) K)).trans (Homeomorph.mulRight (weyl (𝓞 K) K)⁻¹)
      have he : ((MulAut.conj (weyl (𝓞 K) K)).toMonoidHom : GL (Fin 2) (AdeleRing (𝓞 K) K) → GL (Fin 2) (AdeleRing (𝓞 K) K)) = e := by
        funext x; rfl
      rw [he]
      exact e.isOpenMap _ h1
    exact h1.inter h2

  have hcover : S ⊆ ⋃ x : ↥S, (fun y => (x : AdelicGL2 (𝓞 K) K)⁻¹ * y) ⁻¹' P := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    show (x⁻¹ * x) ∈ P
    rw [inv_mul_cancel]; exact (principalLevel (𝓞 K) K N).one_mem
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun x : ↥S => (fun y => (x : AdelicGL2 (𝓞 K) K)⁻¹ * y) ⁻¹' P)
    (fun x => hPo.preimage (continuous_mul_left _)) hcover
  refine ⟨t.card, fun i => ((t.equivFin.symm i : ↥S) : AdelicGL2 (𝓞 K) K), fun i => (t.equivFin.symm i).1.2, ?_⟩
  intro k hk hkf
  have hkS : k ∈ S := ⟨hk, hkf⟩
  obtain ⟨x, hxt, hkx⟩ : ∃ x ∈ t, k ∈ (fun y => (x : AdelicGL2 (𝓞 K) K)⁻¹ * y) ⁻¹' P := by
    simpa only [Set.mem_iUnion, exists_prop] using ht hkS
  refine ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  refine ⟨hkx, ?_⟩
  exact (finiteAdelicGL2Subgroup K).mul_mem ((finiteAdelicGL2Subgroup K).inv_mem x.2.2) hkf

end S_AutomorphicForm_exists_finset_adelicMaximalCompact_finiteAdelic_coset_principalLevel
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_adelicMaximalCompact_finiteAdelic_coset_principalLevel (solution)
