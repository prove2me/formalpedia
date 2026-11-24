-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:51.063107+00:00
-- url     : https://prove2.me/theorems/08015163-a366-462b-bfd9-251a2e60162a
-- title:
--   Wreg Of Subsingleton
-- statement:
--   Definitions and structural lemmas for Wreg Of Subsingleton, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
namespace PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
section General
variable {S : Type u} [CommRing S]
end General
section Piece
variable {R : Type u} [CommRing R] {D : ℕ}
local notation "𝔛" => Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))
theorem homog_mem_pow {a : ℕ} {p : MvPolynomial (Fin D) R} (hp : p.IsHomogeneous a) : p ∈ 𝔛 ^ a := by
  rw [show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff]
  intro d hd
  have h0 := hp (mem_support_iff.1 hd)
  have h1 : d.degree = a := by rw [Finsupp.degree_eq_weight_one]; exact h0
  omega
noncomputable def gmap (a : ℕ) : (MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) →ₗ[MvPolynomial (Fin D) R]
    (MvPolynomial (Fin D) R ⧸ 𝔛 ^ a) :=
  Submodule.factor (Ideal.pow_le_pow_right (Nat.le_succ a))
theorem gmap_mk (a : ℕ) (p : MvPolynomial (Fin D) R) :
    gmap a (Submodule.Quotient.mk p) = Submodule.Quotient.mk p :=
  Submodule.factor_mk (Ideal.pow_le_pow_right (Nat.le_succ a)) p
noncomputable def emb (a : ℕ) : homogeneousSubmodule (Fin D) R a →+ LinearMap.ker (gmap (R := R) (D := D) a) where
  toFun h := ⟨Submodule.Quotient.mk h.1, by
    rw [LinearMap.mem_ker, gmap_mk, Submodule.Quotient.mk_eq_zero]; exact homog_mem_pow h.2⟩
  map_zero' := by ext; simp
  map_add' h h' := by ext; simp
end Piece
end PIW.ENSpec


