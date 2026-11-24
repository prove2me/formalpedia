-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
-- name    : GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:58:09.855127+00:00
-- url     : https://prove2.me/theorems/8bfcc229-2cda-4186-bcf9-588f8c1209a1
-- title:
--   Acyclic
-- statement:
--   Definitions and structural lemmas for Acyclic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules/Acyclic.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory groupCohomology Filter Topology
universe u
section FinTuple
variable {α : Type*} {n : ℕ}
end FinTuple
section Tube
variable {G : Type*} [TopologicalSpace G] [CompactSpace G]
theorem eventually_forall_cons_eq {n : ℕ} {Y : Type*} {f : (Fin (n + 1) → G) → Y}
    (hf : IsLocallyConstant f) (g₀ : Fin n → G) :
    ∀ᶠ g in 𝓝 g₀, ∀ x : G, f (Fin.cons x g) = f (Fin.cons x g₀) := by
  have key := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := g₀)
    (K := (Set.univ : Set G)) (P := fun g x => f (Fin.cons x g) = f (Fin.cons x g₀)) ?_
  · exact key.mono fun g hg x => hg x (Set.mem_univ x)
  intro y _
  have hc1 : Continuous fun z : (Fin n → G) × G => (Fin.cons z.2 z.1 : Fin (n + 1) → G) :=
    Continuous.finCons (A := fun _ => G) continuous_snd continuous_fst
  have hc2 : Continuous fun z : (Fin n → G) × G => (Fin.cons z.2 g₀ : Fin (n + 1) → G) :=
    Continuous.finCons (A := fun _ => G) continuous_snd continuous_const
  have h1 := (hf.comp_continuous hc1).eventually_eq (g₀, y)
  have h2 := (hf.comp_continuous hc2).eventually_eq (g₀, y)
  filter_upwards [h1, h2] with z hz1 hz2
  simp only [Function.comp_apply] at hz1 hz2
  rw [hz1, hz2]
end Tube
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {X : Type u} [AddCommGroup X] [Module k X]
noncomputable def coindHomotopyApply {n : ℕ} (f : (Fin (n + 1) → G) → LocallyConstant G X)
    (hf : IsLocallyConstant f) (g : Fin n → G) : LocallyConstant G X :=
  ⟨fun x => f (Fin.cons x g) 1,
    (hf.comp_continuous (continuous_id.finCons continuous_const)).comp fun φ => φ 1⟩
omit [IsTopologicalGroup G] [CompactSpace G] [AddCommGroup X] [Module k X] in
@[simp]
theorem coindHomotopyApply_apply {n : ℕ} (f : (Fin (n + 1) → G) → LocallyConstant G X)
    (hf : IsLocallyConstant f) (g : Fin n → G) (x : G) :
    coindHomotopyApply f hf g x = f (Fin.cons x g) 1 :=
  rfl
omit [IsTopologicalGroup G] [AddCommGroup X] [Module k X] in
theorem isLocallyConstant_coindHomotopyApply {n : ℕ}
    (f : (Fin (n + 1) → G) → LocallyConstant G X) (hf : IsLocallyConstant f) :
    IsLocallyConstant (coindHomotopyApply f hf) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  filter_upwards [eventually_forall_cons_eq hf g₀] with g hg
  exact LocallyConstant.ext fun x => by simp [hg x]
variable (k X) in

noncomputable def coindHomotopy (n : ℕ) :
    locallyConstantCochains (discreteCoind k G X) (n + 1) →ₗ[k]
      locallyConstantCochains (discreteCoind k G X) n where
  toFun f := ⟨coindHomotopyApply (X := X) f.1 f.2,
    isLocallyConstant_coindHomotopyApply (X := X) f.1 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable (k G X) in

noncomputable def cohomologyZeroDiscreteCoindIso :
    cohomology (discreteCoind k G X) 0 ≅ ModuleCat.of k X :=
  H0Iso (discreteCoind k G X) ≪≫ (invariantsDiscreteCoindEquiv k G X).toModuleIso
end GroundTheory.ProfCoh


