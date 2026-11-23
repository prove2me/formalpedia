-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:22.845797+00:00
-- url     : https://prove2.me/theorems/e8d04118-45d3-461c-a1b6-7102e9826499
-- title:
--   Profinite Integer
-- statement:
--   Definitions and structural lemmas for Profinite Integer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ProfiniteInteger.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
def profiniteIntegers : Subring (∀ n : ℕ+, ZMod n) :=
  ⨅ (m : ℕ+) (n : ℕ+) (h : (m : ℕ) ∣ n),
    RingHom.eqLocus ((ZMod.castHom h (ZMod m)).comp (Pi.evalRingHom (fun k : ℕ+ => ZMod k) n))
      (Pi.evalRingHom (fun k : ℕ+ => ZMod k) m)
abbrev ProfiniteInteger : Type := profiniteIntegers
@[inherit_doc] scoped notation "ℤ̂" => ProfiniteInteger
theorem mem_profiniteIntegers {x : ∀ n : ℕ+, ZMod n} :
    x ∈ profiniteIntegers ↔
      ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), ZMod.castHom h (ZMod m) (x n) = x m := by
  simp [profiniteIntegers, Subring.mem_iInf, RingHom.mem_eqLocus]
namespace ProfiniteInteger
def proj (n : ℕ+) : ℤ̂ →+* ZMod n :=
  (Pi.evalRingHom (fun k : ℕ+ => ZMod k) n).comp profiniteIntegers.subtype
@[simp] theorem proj_apply (n : ℕ+) (x : ℤ̂) : proj n x = (x : ∀ k : ℕ+, ZMod k) n := rfl
@[ext] theorem ext {x y : ℤ̂} (h : ∀ n, proj n x = proj n y) : x = y :=
  Subtype.ext (funext h)
@[simp] theorem proj_intCast (n : ℕ+) (m : ℤ) : proj n (m : ℤ̂) = m := map_intCast _ m
theorem isClosed_profiniteIntegers :
    IsClosed (profiniteIntegers : Set (∀ n : ℕ+, ZMod n)) := by
  have : (profiniteIntegers : Set (∀ n : ℕ+, ZMod n)) =
      ⋂ (m : ℕ+) (n : ℕ+) (h : (m : ℕ) ∣ n), {x | ZMod.castHom h (ZMod m) (x n) = x m} := by
    ext x
    simp only [SetLike.mem_coe, mem_profiniteIntegers, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  refine isClosed_iInter fun m => isClosed_iInter fun n => isClosed_iInter fun h => ?_
  exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n)) (continuous_apply m)
instance : CompactSpace ℤ̂ :=
  isCompact_iff_compactSpace.mp isClosed_profiniteIntegers.isCompact
instance : CharZero ℤ̂ := by
  refine charZero_of_inj_zero fun n hn => ?_
  have h := congrArg (proj n.succPNat) hn
  rw [map_natCast, map_zero, ZMod.natCast_eq_zero_iff, Nat.succPNat_coe] at h
  exact Nat.eq_zero_of_dvd_of_lt h (Nat.lt_succ_self n)
end ProfiniteInteger
end GroundTheory.LocalField.Abstract


