-- Prove2me | solution 1 for AlgebraicCurve.isIntegral_adjoin_intermediateField_mk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5d5e4752-c1b9-5579-8f70-e09bba79b803

import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.FieldTheory.IntermediateField.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk

set_option autoImplicit false

theorem solution {L F : Type*} [Field L] [Field F] [Algebra L F] (E : IntermediateField L F) {j x : F} (hj : j ∈ E) (hx : x ∈ E) (h : IsIntegral (Algebra.adjoin L {j}) x) : IsIntegral (Algebra.adjoin L {(⟨j, hj⟩ : E)}) (⟨x, hx⟩ : E) := by
  have hmapeq : (Algebra.adjoin L {(⟨j, hj⟩ : E)}).map E.val
      = Algebra.adjoin L {j} := by
    rw [← Algebra.adjoin_image, Set.image_singleton]
    rfl
  let ψfwd : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) →ₐ[L] ↥(Algebra.adjoin L {j}) :=
    (Subalgebra.equivOfEq _ _ hmapeq).toAlgHom.comp
      (E.val.subalgebraMap (Algebra.adjoin L {(⟨j, hj⟩ : E)}))
  have hcoeF : ∀ b : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}),
      ((ψfwd b : ↥(Algebra.adjoin L {j})) : F) = ((b : E) : F) := fun b => rfl
  have hinjE : Function.Injective ((↑) : E → F) := Subtype.coe_injective
  have hbij : Function.Bijective ψfwd := by
    constructor
    · intro a b hab
      exact Subtype.ext (hinjE (by
        have := congrArg (Subtype.val : ↥(Algebra.adjoin L {j}) → F) hab
        rwa [hcoeF a, hcoeF b] at this))
    · exact (Subalgebra.equivOfEq _ _ hmapeq).surjective.comp
        (E.val.subalgebraMap_surjective _)
  let e := RingEquiv.ofBijective ψfwd hbij
  have hcoe : ∀ a : ↥(Algebra.adjoin L {j}),
      (((e.symm a : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)})) : E) : F) = (a : F) := by
    intro a
    have h2 : ψfwd (e.symm a) = a := e.apply_symm_apply a
    calc (((e.symm a : ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)})) : E) : F)
        = ((ψfwd (e.symm a) : ↥(Algebra.adjoin L {j})) : F) := (hcoeF _).symm
      _ = (a : F) := by rw [h2]
  letI : Algebra ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) F :=
    ((algebraMap E F).comp (algebraMap ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) E)).toAlgebra
  have hxT : IsIntegral ↥(Algebra.adjoin L {(⟨j, hj⟩ : E)}) x :=
    IsIntegral.map_of_comp_eq e.symm.toRingHom (RingHom.id F)
      (by ext a; exact hcoe a) h
  let f : E →ₐ[↥(Algebra.adjoin L {(⟨j, hj⟩ : E)})] F :=
    { toRingHom := (E.val : E →+* F), commutes' := fun t => rfl }
  have hinjf : Function.Injective f := hinjE
  exact (isIntegral_algHom_iff f hinjf).mp hxT

end S_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk
end P2MW
export P2MW.S_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk (solution)
