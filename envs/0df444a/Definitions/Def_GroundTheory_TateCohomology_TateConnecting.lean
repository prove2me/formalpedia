-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_TateConnecting
-- name    : GroundTheory_TateCohomology_TateConnecting
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:19.030677+00:00
-- url     : https://prove2.me/theorems/abb8f678-c5d2-48a1-b8ad-4912f74d41b6
-- title:
--   Tate Connecting
-- statement:
--   Definitions and structural lemmas for Tate Connecting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336


set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
namespace GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
noncomputable abbrev tateIsoH (A : Rep k G) (p : ℤ) (n : ℕ) [NeZero n] (hp : p = n) :
    tateCohomology A p ≅ groupCohomology A n :=
  (tateComplexConnectData A).homologyIsoPos n p hp
theorem tate_d_iCycles (A : Rep k G) (n : ℕ) (z : (tateComplex A).cycles n) :
    (inhomogeneousCochains.d A n).hom (((tateComplex A).iCycles n).hom z) = 0 := by
  have h := congr(($((tateComplex A).iCycles_d n (n + 1))).hom z)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, tateComplex_d_ofNat,
    inhomogeneousCochains.d_def] at h
  exact h
noncomputable def tateCyclesMk (A : Rep k G) (i : ℤ) (x : (tateComplex A).X i)
    (hx : ((tateComplex A).d i (i + 1)).hom x = 0) : (tateComplex A).cycles i :=
  (tateComplex A).cyclesMk x (i + 1) (by simp) hx
noncomputable abbrev tδ {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (i j : ℤ)
    (hij : i + 1 = j) :
    tateCohomology S.X₃ i ⟶ tateCohomology S.X₁ j :=
  (TateCohomology.map_tateComplexFunctor_shortExact hS).δ i j hij
section Elements
variable {X Y Z : Rep k G}
variable {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
include hS
end Elements
section Anticomm
variable (Q : ShortComplex (ShortComplex (Rep k G)))
  (hR₁ : Q.X₁.ShortExact) (hR₂ : Q.X₂.ShortExact) (hR₃ : Q.X₃.ShortExact)
  (hC₁ : (Q.map ShortComplex.π₁).ShortExact) (hC₂ : (Q.map ShortComplex.π₂).ShortExact)
  (hC₃ : (Q.map ShortComplex.π₃).ShortExact)
end Anticomm
end GroundTheory.GroupCoh


