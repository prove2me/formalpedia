-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:42.213117+00:00
-- url     : https://prove2.me/theorems/7624c9dc-da24-44f5-a2d7-3100c8aeddff
-- title:
--   PSerre Poly Laurent
-- statement:
--   Definitions and structural lemmas for PSerre Poly Laurent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
namespace LaurentLoc
variable (S : Type u) [CommRing S] (N : ℕ)
def expHom : (Fin (N + 1) →₀ ℕ) →+ (Fin (N + 1) → ℤ) where
  toFun := expToInt N
  map_zero' := by funext j; simp [expToInt]
  map_add' e f := by funext j; simp [expToInt]
abbrev LRing : Type u := AddMonoidAlgebra S (Fin (N + 1) → ℤ)
def toL : Poly S N →+* LRing S N := AddMonoidAlgebra.mapDomainRingHom S (expHom N)
variable {S N}
theorem toL_monomial (f : Fin (N + 1) →₀ ℕ) (r : S) :
    toL S N (monomial f r) = AddMonoidAlgebra.single (expToInt N f) r :=
  AddMonoidAlgebra.mapDomain_single
theorem mem_monos_iff {I : Finset (Fin (N + 1))} {s : Poly S N} :
    s ∈ monos I → ∃ f : Fin (N + 1) →₀ ℕ, (∀ j ∉ I, f j = 0) ∧ s = monomial f 1 := by
  intro hs
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Finsupp.single i 1, fun j hj => ?_, rfl⟩
    rw [Finsupp.single_apply, if_neg]
    rintro rfl; exact hj hi
  | one => exact ⟨0, fun _ _ => rfl, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    refine ⟨f + g, fun j hj => by simp [hf j hj, hg j hj], ?_⟩
    rw [monomial_mul, one_mul]
theorem isUnit_toL {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) : IsUnit (toL S N s) := by
  obtain ⟨f, -, rfl⟩ := mem_monos_iff hs
  rw [toL_monomial]
  refine isUnit_iff_exists_inv.mpr ⟨AddMonoidAlgebra.single (-expToInt N f) 1, ?_⟩
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
  rfl
abbrev algP : Algebra (Poly S N) (LRing S N) := (toL S N).toAlgebra
attribute [local instance] algP
instance : IsScalarTower S (Poly S N) (LRing S N) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap S (LRing S N) r = toL S N (monomial 0 r)
    rw [toL_monomial]
    have : expToInt N 0 = 0 := funext fun j => by simp [expToInt]
    rw [this]
    rfl
theorem isUnit_end (I : Finset (Fin (N + 1))) (s : monos (S := S) I) :
    IsUnit (algebraMap (Poly S N) (Module.End (Poly S N) (LRing S N)) s) := by
  rw [Module.End.isUnit_iff]
  have hu := (isUnit_toL s.2).unit.mulLeft_bijective
  exact hu
def iotaP (I : Finset (Fin (N + 1))) : LocMod S N (Poly S N) I →ₗ[Poly S N] LRing S N :=
  LocalizedModule.lift (monos I) (Algebra.linearMap (Poly S N) (LRing S N)) (isUnit_end I)
end LaurentLoc
namespace LaurentLoc
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP
def iota (I : StdCell N) : LocMod S N (Poly S N) I.1 →ₗ[S] Laurent S N :=
  (AddMonoidAlgebra.coeffLinearEquiv S).toLinearMap ∘ₗ (iotaP (S := S) (N := N) I.1).restrictScalars S
end LaurentLoc
namespace LaurentLoc
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP
end LaurentLoc
end
end GroundTheory.Heights₂.Heights.Kleiman


