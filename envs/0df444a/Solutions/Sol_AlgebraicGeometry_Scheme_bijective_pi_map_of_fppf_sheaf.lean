-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.bijective_pi_map_of_fppf_sheaf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0ea206bf-d509-5397-8dfb-d6b29190310b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_bijective_pi_map_of_fppf_sheaf

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem FinProdAux.isIso_sigmaSpec {ι : Type u} [Finite ι] (A : ι → CommRingCat.{u}) :
    IsIso (AlgebraicGeometry.sigmaSpec A) := inferInstance

theorem solution
    (E : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1}) {ι : Type u} [Finite ι] (A : ι → CommRingCat.{u}) :
    Function.Bijective (fun (x : ToType (E.obj.obj (op (Spec (CommRingCat.of (∀ i, A i)))))) (i : ι) =>
      E.obj.map (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i => A i) i))).op x) := by
  classical

  let F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) := E.obj ⋙ forget AddCommGrpCat.{u + 1}
  have hF : Presieve.IsSheaf Scheme.fppfTopology.{u} F :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.fppfTopology.{u} E.obj (forget AddCommGrpCat.{u + 1})).mp
        E.property)
  have hle : Scheme.zariskiTopology.{u} ≤ Scheme.fppfTopology.{u} :=
    Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage
  have hZ : Presieve.IsSheaf Scheme.zariskiTopology.{u} F := Presieve.isSheaf_of_le F hle hF
  haveI : PreservesLimitsOfShape (Discrete ι) F := preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hZ

  let X : ι → Scheme.{u} := fun i => Spec (A i)
  let c : Cofan X := Cofan.mk (Spec (CommRingCat.of (∀ i, A i)))
    (fun i => Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i => A i) i)))
  haveI hiso : IsIso (AlgebraicGeometry.sigmaSpec A) := FinProdAux.isIso_sigmaSpec A
  have hc : IsColimit c := (coproductIsCoproduct X).ofIsoColimit
    (Cocone.ext (@asIso _ _ _ _ (AlgebraicGeometry.sigmaSpec A) hiso) (by rintro ⟨i⟩; exact ι_sigmaSpec A i))

  have hl : IsLimit (F.mapCone c.op) := isLimitOfPreserves F (Cofan.IsColimit.op hc)
  let t := Types.isLimitEquivSections hl

  have hsec : ∀ (v : ∀ i, F.obj (op (X i))),
      (fun j : Discrete ι => (v j.as : ((Discrete.functor fun i => op (X i)) ⋙ F).obj j)) ∈
        ((Discrete.functor fun i => op (X i)) ⋙ F).sections := by
    intro v j j' f
    obtain ⟨i⟩ := j
    obtain ⟨i'⟩ := j'
    obtain rfl : i = i' := Discrete.eq_of_hom f
    rw [show f = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    rfl
  change Function.Bijective (fun (x : F.obj (op c.pt)) (i : ι) => F.map (c.inj i).op x)
  have key : ∀ (x : F.obj (op c.pt)) (i : ι), F.map (c.inj i).op x = (t x).1 ⟨i⟩ := fun x i =>
    (Types.isLimitEquivSections_apply hl ⟨i⟩ x).symm
  constructor
  · intro x y hxy
    apply t.injective
    refine Subtype.ext (funext fun ⟨i⟩ => ?_)
    rw [← key, ← key]
    exact congrFun hxy i
  · intro v
    refine ⟨t.symm ⟨_, hsec v⟩, funext fun i => ?_⟩
    show F.map (c.inj i).op (t.symm ⟨_, hsec v⟩) = v i
    rw [key, Equiv.apply_symm_apply]

end S_AlgebraicGeometry_Scheme_bijective_pi_map_of_fppf_sheaf
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_bijective_pi_map_of_fppf_sheaf (solution)
