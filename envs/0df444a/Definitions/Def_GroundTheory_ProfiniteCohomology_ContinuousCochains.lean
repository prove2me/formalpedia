-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
-- name    : GroundTheory_ProfiniteCohomology_ContinuousCochains
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:47:40.279737+00:00
-- url     : https://prove2.me/theorems/a7086d02-981e-4dd7-b923-86aecb853500
-- title:
--   Continuous Cochains
-- statement:
--   Definitions and structural lemmas for Continuous Cochains, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isLocallyConstant_apply
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
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
def locallyConstantCochains (A : Rep.{u} k G) (n : ℕ) : Submodule k ((Fin n → G) → A) where
  carrier := {f | IsLocallyConstant f}
  zero_mem' := IsLocallyConstant.const 0
  add_mem' hf hg := IsLocallyConstant.add hf hg
  smul_mem' r _ hf := hf.comp (r • ·)
variable [IsTopologicalGroup G]
theorem continuous_contractNth {n : ℕ} (j : Fin (n + 1)) :
    Continuous fun g : Fin (n + 1) → G => Fin.contractNth j (· * ·) g := by
  refine continuous_pi fun i => ?_
  simp only [Fin.contractNth]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).mul (continuous_apply _)
  · exact continuous_apply _
theorem isLocallyConstant_d (A : Rep.{u} k G) [IsDiscreteRep A] {n : ℕ}
    {f : (Fin n → G) → A} (hf : IsLocallyConstant f) :
    IsLocallyConstant ((inhomogeneousCochains.d A n).hom f) := by
  have h1 : IsLocallyConstant fun g : Fin (n + 1) → G => A.ρ (g 0) (f fun i => g i.succ) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have htail : Continuous fun g : Fin (n + 1) → G => fun i : Fin n => g i.succ :=
      continuous_pi fun i => continuous_apply _
    have hev1 : ∀ᶠ y in nhds g, f (fun i => y i.succ) = f (fun i => g i.succ) :=
      htail.continuousAt.eventually (hf.eventually_eq _)
    have hev2 : ∀ᶠ y in nhds g,
        A.ρ (y 0) (f fun i => g i.succ) = A.ρ (g 0) (f fun i => g i.succ) :=
      (continuous_apply 0).continuousAt.eventually
        ((isLocallyConstant_apply A (f fun i => g i.succ)).eventually_eq (g 0))
    filter_upwards [hev1, hev2] with y h1 h2
    rw [h1, h2]
  have h2 : ∀ j : Fin (n + 1), IsLocallyConstant fun g : Fin (n + 1) → G =>
      (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := fun j =>
    (hf.comp_continuous (continuous_contractNth j)).comp _
  have h3 : IsLocallyConstant fun g : Fin (n + 1) → G => Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := by
    have : (fun g : Fin (n + 1) → G => Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)) =
        Finset.univ.sum fun j : Fin (n + 1) => fun g : Fin (n + 1) → G =>
          (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := by
      ext g
      simp [Finset.sum_apply]
    rw [this]
    exact Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb)
      (IsLocallyConstant.const 0) fun j _ => h2 j
  have : (inhomogeneousCochains.d A n).hom f = fun g =>
      A.ρ (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := by
    ext g
    simp [inhomogeneousCochains.d_hom_apply]
  rw [this]
  exact h1.add h3
theorem d_mem_locallyConstantCochains (A : Rep.{u} k G) [IsDiscreteRep A] {n : ℕ}
    {f : (Fin n → G) → A} (hf : f ∈ locallyConstantCochains A n) :
    (inhomogeneousCochains.d A n).hom f ∈ locallyConstantCochains A (n + 1) :=
  isLocallyConstant_d A hf
noncomputable def dLocallyConstant (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) :
    ModuleCat.of k (locallyConstantCochains A n) ⟶
      ModuleCat.of k (locallyConstantCochains A (n + 1)) :=
  ModuleCat.ofHom ((inhomogeneousCochains.d A n).hom.restrict
    fun _ hf => d_mem_locallyConstantCochains A hf)
theorem dLocallyConstant_comp (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) :
    dLocallyConstant A n ≫ dLocallyConstant A (n + 1) = 0 := by
  ext f : 2
  apply Subtype.ext
  have := congrArg (fun φ => φ.hom f.1) (inhomogeneousCochains.d_comp_d (A := A) (n := n))
  exact this
noncomputable def cochainsComplex (A : Rep.{u} k G) [IsDiscreteRep A] :
    CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (locallyConstantCochains A n))
    (fun n => dLocallyConstant A n) fun n => dLocallyConstant_comp A n
theorem cochainsComplex_d (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) :
    (cochainsComplex A).d n (n + 1) = dLocallyConstant A n := by
  simp [cochainsComplex]
noncomputable def cochainsComplexι (A : Rep.{u} k G) [IsDiscreteRep A] :
    cochainsComplex A ⟶ inhomogeneousCochains A :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (locallyConstantCochains A n).subtype) fun n => by
    rw [cochainsComplex_d, inhomogeneousCochains.d_def]
    ext f : 2
    rfl
instance (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) : Mono ((cochainsComplexι A).f n) :=
  (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
noncomputable abbrev cocycles (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) : ModuleCat k :=
  (cochainsComplex A).cycles n
noncomputable def cohomology (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) : ModuleCat k :=
  (cochainsComplex A).homology n
noncomputable abbrev cohomologyπ (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) :
    cocycles A n ⟶ cohomology A n :=
  (cochainsComplex A).homologyπ n
end GroundTheory.ProfCoh


