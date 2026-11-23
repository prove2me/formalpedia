-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormSubgroupOpen
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormSubgroupOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:10.909507+00:00
-- url     : https://prove2.me/theorems/136289d5-1d40-4d6e-ad9e-11140ea0d3ed
-- title:
--   Norm Subgroup Open
-- statement:
--   Definitions and structural lemmas for Norm Subgroup Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormSubgroupOpen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.zlW :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → (R : Type) → [inst_1 : CommRing R] → [CharP R l] → ℤ_[l] →+* WittVector l R :=
    fun (l : ℕ) [Fact (Nat.Prime l)] (R : Type) [CommRing R] [CharP R l] ↦
      (WittVector.map (ZMod.castHom (dvd_refl l) R)).comp (WittVector.equiv l).symm.toRingHom
namespace UpperTheory.Reformulated.B.WittVectorTrivializingMatrix
section
variable {p : ℕ} [hp : Fact (Nat.Prime p)] {G : Type} [Group G] {R : Type} [CommRing R]
def Nm (ρ : G →* R ≃+* R) (p m : ℕ) : Subgroup G where
  carrier := {g | ∀ y : R, y ^ p ^ m = y → ρ g y = y}
  mul_mem' := by
    intro a b ha hb y hy
    rw [map_mul]
    change ρ a (ρ b y) = y
    rw [hb y hy, ha y hy]
  one_mem' := by intro y _; rw [map_one]; rfl
  inv_mem' := by
    intro a ha y hy
    have : ρ a⁻¹ (ρ a y) = y := by
      change (ρ a⁻¹ * ρ a) y = y
      rw [← map_mul, inv_mul_cancel, map_one]; rfl
    rwa [ha y hy] at this
noncomputable def sg (p : ℕ) [Fact (Nat.Prime p)] (ρ : G →* R ≃+* R) (g : G) :
    WittVector p R →+* WittVector p R := WittVector.map (ρ g).toRingHom
variable [CharP R p]
noncomputable def Sm (p : ℕ) [Fact (Nat.Prime p)] (R : Type) [CommRing R] [CharP R p]
    (m : ℕ) : Subring (WittVector p R) :=
  (WittVector.map (iterateFrobenius R p m)).eqLocus (RingHom.id _)
noncomputable def Km (p : ℕ) [Fact (Nat.Prime p)] (R : Type) [CommRing R] [CharP R p]
    (m : ℕ) : Subring R :=
  (iterateFrobenius R p m).eqLocus (RingHom.id _)
variable [IsDomain R]
noncomputable def chi (ρ : G →* R ≃+* R) (p : ℕ) [Fact (Nat.Prime p)] [CharP R p] (m : ℕ)
    (q : G ⧸ Nm ρ p m) : Km p R m →+* R := (ρ q.out).toRingHom.comp (Km p R m).subtype
noncomputable def Mw (p : ℕ) [Fact (Nat.Prime p)] (R : Type) [CommRing R] [CharP R p]
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (g : G) :
    Matrix (Fin r) (Fin r) (WittVector p R) := (M g).map (zlW p R)
def Good (ρ : G →* R ≃+* R) {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (n : ℕ)
    (W : Matrix (Fin r) (Fin r) (WittVector p R)) : Prop :=
  (∃ m, 0 < m ∧ ∀ i j, W i j ∈ Sm p R m) ∧
    ∀ g, (Mw p R M g * W.map (sg p ρ g)).map (WittVector.truncate n) = W.map (WittVector.truncate n)
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
end
end UpperTheory.Reformulated.B.WittVectorTrivializingMatrix


