-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FactorMemCocyclesPowQuot
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FactorMemCocyclesPowQuot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:31.445751+00:00
-- url     : https://prove2.me/theorems/30869999-4627-4595-afad-22d5f52b54f5
-- title:
--   Factor Mem Cocycles Pow Quot
-- statement:
--   Definitions and structural lemmas for Factor Mem Cocycles Pow Quot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FactorMemCocyclesPowQuot.lean

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal
open Formalism.NG (KO)
noncomputable section
namespace GlobalTheory.LocDualInt
section Pow
variable {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module O M]
def powSub (a : O) (n : ℕ) : Submodule O M := LinearMap.range ((a ^ n) • LinearMap.id : M →ₗ[O] M)
theorem mem_powSub {a : O} {n : ℕ} {x : M} : x ∈ powSub (M := M) a n ↔ ∃ y : M, a ^ n • y = x := by
  simp [powSub]
theorem powSub_anti (a : O) {m n : ℕ} (h : m ≤ n) : powSub (M := M) a n ≤ powSub a m := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_powSub.1 hx
  refine mem_powSub.2 ⟨a ^ (n - m) • y, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' h]
theorem powSub_stable (ρ : Representation O G M) (a : O) (n : ℕ) (g : G) (x : M)
    (hx : x ∈ powSub (M := M) a n) : ρ g x ∈ powSub (M := M) a n := by
  obtain ⟨y, rfl⟩ := mem_powSub.1 hx
  exact mem_powSub.2 ⟨ρ g y, by rw [map_smul]⟩
def quotRep (ρ : Representation O G M) (a : O) (n : ℕ) :
    Representation O G (M ⧸ powSub (M := M) a n) where
  toFun g := (powSub a n).mapQ (powSub a n) (ρ g) (fun x hx => powSub_stable ρ a n g x hx)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_mul' g h := by
    apply Submodule.linearMap_qext
    ext x
    simp [Module.End.mul_apply]
def qlift {N : Submodule O M} (z : M ⧸ N) : M := (Submodule.Quotient.mk_surjective N z).choose
end Pow
section TopPow
variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul O M]
end TopPow
end GlobalTheory.LocDualInt
noncomputable section
namespace GlobalTheory.LocDualInt
section Lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {G : Type} [Group G] [TopologicalSpace G]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT')
def cupMod (c : G → VT ⧸ D.T) (a : O) (n : ℕ) (z : G → ↥D.T' ⧸ powSub (M := ↥D.T') a n) :
    G × G → KO O :=
  fun p => pairKO D.bT D.T (c p.1) (D.ρTl' p.1 (qlift (z p.2)))
end Lat
end GlobalTheory.LocDualInt


