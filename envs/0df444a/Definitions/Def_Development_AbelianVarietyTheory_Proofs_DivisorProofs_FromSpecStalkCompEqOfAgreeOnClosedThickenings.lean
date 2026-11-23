-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FromSpecStalkCompEqOfAgreeOnClosedThickenings
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FromSpecStalkCompEqOfAgreeOnClosedThickenings
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:27.640296+00:00
-- url     : https://prove2.me/theorems/0554f618-798d-48dc-ac76-71c26983e694
-- title:
--   From Spec Stalk Comp Eq Of Agree On Closed Thickenings
-- statement:
--   Definitions and structural lemmas for From Spec Stalk Comp Eq Of Agree On Closed Thickenings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FromSpecStalkCompEqOfAgreeOnClosedThickenings.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.ThickStalkEq
theorem isLocalHom_mk {A : Type} [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalHom (Ideal.Quotient.mk I) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  obtain ⟨v, hv⟩ := ha
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑v⁻¹ : A ⧸ I)
  have h1 : Ideal.Quotient.mk I (a * b - 1) = 0 := by
    rw [map_sub, map_mul, hb, ← hv]; simp
  rw [Ideal.Quotient.eq_zero_iff_mem] at h1
  have hm : a * b - 1 ∈ maximalIdeal A := le_maximalIdeal hI h1
  have ha' : a * b ∈ maximalIdeal A := Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).2 hna)
  have h2 : (1 : A) ∈ maximalIdeal A := by simpa using Ideal.sub_mem _ ha' hm
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h2)
theorem pow_succ_ne_top (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    maximalIdeal A ^ (e + 1) ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e))
instance (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    Nontrivial (A ⧸ maximalIdeal A ^ (e + 1)) :=
  Ideal.Quotient.nontrivial_iff.2 (pow_succ_ne_top A e)
instance (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    IsLocalRing (A ⧸ maximalIdeal A ^ (e + 1)) :=
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
instance (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1))) :=
  isLocalHom_mk _ (pow_succ_ne_top A e)
end GlobalTheory.ThickStalkEq
namespace GlobalTheory.ThickStalkEq
end GlobalTheory.ThickStalkEq


