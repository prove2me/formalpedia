-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:36:00.670727+00:00
-- url     : https://prove2.me/theorems/c6ca006b-7add-433e-8183-14304df9f0aa
-- title:
--   PTilde Tail Loc
-- statement:
--   Definitions and structural lemmas for PTilde Tail Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_coneSingle_20bc626224db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_isHomogeneous_bb0f48dbdc12

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
universe u w
section Loc
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem aeval_ne_zero_of_mem_monos_support {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    {s : Poly S N} (hs : s ∈ monos I) : aeval x s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [aeval_X]
    exact (mem_support x).mp (hI hi)
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_ne_zero ha hb
theorem isUnit_coneLaurent_of_mem_monos {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    {s : Poly S N} (hs : s ∈ monos I) : IsUnit (coneLaurent S x s) := by
  obtain ⟨e, he⟩ := monos_isHomogeneous hs
  rw [coneLaurent_of_isHomogeneous he]
  exact isUnit_coneSingle (S := S) (x := x) e (aeval_ne_zero_of_mem_monos_support hI hs)
variable (M : FinGradedSub (S := S) (x := x) Ω)
def locCone (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    LocMod S N M.coneSub I →ₗ[Poly S N] ConeLaurent S x :=
  LocalizedModule.lift (monos I) M.coneSub.subtype fun s => by
    rw [Module.End.isUnit_iff]
    exact IsUnit.isUnit_iff_mulLeft_bijective.mp (isUnit_coneLaurent_of_mem_monos hI s.2)
def tildeGens (c : ℤ) (I : Chart x) : Set Ω :=
  {y | ∃ (m : Ω) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I.1 ∧ s.IsHomogeneous e ∧ m ∈ M.piece a ∧
    a - e = c ∧ y = (aeval x s)⁻¹ • m}
end Loc
end
end GroundTheory.Heights₂.Heights.Kleiman


