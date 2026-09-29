-- Prove2me | solution 1 for AlgebraicCurve.Place.mem_toValuationSubring_of_isIntegral_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/64a65cfd-323a-5a4b-bde4-2d6044710ccb

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Valuation.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin

set_option autoImplicit false

open AlgebraicCurve

namespace ModularCurve

namespace QexpN

private def placeSubalgebra {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    Subalgebra K F :=
  { v.toValuationSubring.toSubring.toSubsemiring with algebraMap_mem' := v.algebraMap_mem' }

private theorem mem_placeSubalgebra {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {y : F} :
    y ∈ placeSubalgebra v ↔ y ∈ v.toValuationSubring := Iff.rfl

private theorem valuationSubring_integers {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) :
    (v.toValuationSubring.valuation).Integers v.toValuationSubring :=
  { hom_inj := Subtype.coe_injective
    map_le_one := fun a => v.toValuationSubring.valuation_le_one a
    exists_of_le_one := fun {r} hr =>
      ⟨⟨r, v.toValuationSubring.mem_of_valuation_le_one r hr⟩, rfl⟩ }

private theorem mem_of_isIntegral_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring)
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring := by
  have hle : Algebra.adjoin K {j} ≤ placeSubalgebra v :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ((mem_placeSubalgebra v).mpr hj))
  let φ' : ↥(Algebra.adjoin K {j}) →+* ↥(v.toValuationSubring) :=
    { toFun := fun a => ⟨(a : F), (mem_placeSubalgebra v).mp (hle a.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hOx : IsIntegral (↥v.toValuationSubring) x :=
    IsIntegral.map_of_comp_eq φ' (RingHom.id F) (by ext a; rfl) hx
  exact v.toValuationSubring.mem_of_valuation_le_one x
    ((valuationSubring_integers v).isIntegral_iff_v_le_one.mp hOx)

end QexpN

end ModularCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring) (hx : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring :=
  ModularCurve.QexpN.mem_of_isIntegral_adjoin v hj hx

end S_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
end P2MW
export P2MW.S_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin (solution)
