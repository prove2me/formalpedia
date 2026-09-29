-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/086224f1-09b4-5c2c-b66e-387db70d4590

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_mem_of_forall_mem_iff_of_subset
import Theorems.Thm_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental
import Theorems.Thm_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers

set_option autoImplicit false
set_option maxHeartbeats 8000000

open AlgebraicCurve IsLocalRing Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) f)
    (h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) → f ∈ V)
    (j : ℕ) :
    (((minpoly (Algebra.adjoin L ({(x : F)} : Set F)) f).coeff j :
      Algebra.adjoin L ({(x : F)} : Set F)) : F) ∈ R.integers := by
  classical

  have hxL : Transcendental L (x : F) :=
    RegularProlongation.transcendental_of_residue_transcendental A R x hx

  haveI hIC : IsIntegrallyClosed (Algebra.adjoin L ({(x : F)} : Set F)) :=
    Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental (x : F) hxL

  have hfV : ∀ V : ValuationSubring F,
      (∀ e ∈ (IntermediateField.adjoin L {(x : F)}).toSubfield, e ∈ R.integers → e ∈ V) →
      f ∈ V := by
    intro V hKV
    exact ValuationSubring.mem_of_forall_mem_iff_of_subset
      (IntermediateField.adjoin L {(x : F)}).toSubfield R.integers V hKV f
      (fun V' hV' => h₃ V' (fun e he => hV' e he))

  set S : Subring F :=
    (IntermediateField.adjoin L {(x : F)}).toSubfield.toSubring ⊓ R.integers.toSubring with hS
  have hfintS : IsIntegral S f := by
    have hmem : f ∈ (integralClosure (Subring.closure (S : Set F)) F).toSubring := by
      rw [← iInf_valuationSubring_superset]
      simp only [Subring.mem_iInf]
      rintro ⟨V, hSV⟩
      refine hfV V (fun e heK heO => ?_)
      exact hSV (Subring.mem_inf.mpr ⟨heK, heO⟩)
    have hclS : Subring.closure (S : Set F) = S := Subring.closure_eq S
    exact hclS ▸ hmem

  set W : ValuationSubring (IntermediateField.adjoin L {(x : F)}) :=
    R.integers.comap (IntermediateField.adjoin L {(x : F)}).toSubfield.subtype with hW
  letI algWF : Algebra (↥W) F :=
    RingHom.toAlgebra ((IntermediateField.adjoin L {(x : F)}).toSubfield.subtype.comp W.subtype)
  letI towWKF : IsScalarTower (↥W) (↥(IntermediateField.adjoin L {(x : F)})) F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let φSW : S →+* W :=
    { toFun := fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hfintW : IsIntegral W f := by
    refine hfintS.map_of_comp_eq φSW (RingHom.id F) ?_
    ext e; rfl

  have hKcoeff : ∀ i, ((minpoly (IntermediateField.adjoin L {(x : F)}) f).coeff i : F)
      ∈ R.integers := by
    intro i
    have heq : minpoly (IntermediateField.adjoin L {(x : F)}) f =
        (minpoly W f).map (algebraMap W (IntermediateField.adjoin L {(x : F)})) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' _ hfintW
    rw [heq, Polynomial.coeff_map]
    exact ((minpoly W f).coeff i).2

  have hqK : minpoly (IntermediateField.adjoin L {(x : F)}) f =
      (minpoly (Algebra.adjoin L ({(x : F)} : Set F)) f).map
        (algebraMap (Algebra.adjoin L ({(x : F)} : Set F))
          (IntermediateField.adjoin L {(x : F)})) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' _ hint
  have hcoe : (((minpoly (Algebra.adjoin L ({(x : F)} : Set F)) f).coeff j :
      Algebra.adjoin L ({(x : F)} : Set F)) : F) =
      ((minpoly (IntermediateField.adjoin L {(x : F)}) f).coeff j : F) := by
    rw [hqK, Polynomial.coeff_map]
    rfl
  rw [hcoe]
  exact hKcoeff j

end S_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers (solution)
