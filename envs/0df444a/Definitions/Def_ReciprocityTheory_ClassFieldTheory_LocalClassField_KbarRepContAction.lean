-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KbarRepContAction
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_KbarRepContAction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:25.629082+00:00
-- url     : https://prove2.me/theorems/157c6cc3-55bf-4ad4-b9f9-9c4bdab0dfc6
-- title:
--   Kbar Rep Cont Action
-- statement:
--   Definitions and structural lemmas for Kbar Rep Cont Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/KbarRepContAction.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
theorem kbarRep_contAction : ReciprocityTheory.Gal.ContAction (kbarRep p K) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  show Continuous fun q : GK p K × KbarMult p => kbarRep p K q.1 q.2
  rw [continuous_prod_of_discrete_right]
  intro y
  rw [continuous_discrete_rng]
  intro x
  rw [isOpen_iff_mem_nhds]
  intro g0 hg0
  have hop := stabilizer_isOpen_of_isIntegral (K := K) (L := PadicAlgCl p)
    (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
  have hn : (fun g : GK p K => g0⁻¹ * g) ⁻¹' (MulAction.stabilizer (GK p K)
      (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) : Set (GK p K)) ∈ nhds g0 :=
    (hop.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : (g0⁻¹ * g) (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
      = (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := hg
  have hgg : g (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
      = g0 (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := by
    have := congrArg g0 hg'
    rw [AlgEquiv.mul_apply] at this
    rw [← this]
    exact (g0.apply_symm_apply _).symm
  have hxy : kbarRep p K g y = kbarRep p K g0 y := Units.ext hgg
  show kbarRep p K g y = x
  rw [hxy]
  exact hg0
noncomputable def kbarT : TRep ℤ (GK p K) where
  V := KbarMult p
  rho := kbarRep p K
  cont := kbarRep_contAction p K
scoped instance : DiscreteTopology (kbarT p K).V := inferInstanceAs (DiscreteTopology (KbarMult p))
end ReciprocityTheory.DiscreteGroups.LocalClassField


