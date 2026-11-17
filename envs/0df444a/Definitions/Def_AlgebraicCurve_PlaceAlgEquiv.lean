-- Prove2me | Definitions.Def_AlgebraicCurve_PlaceAlgEquiv
-- name    : AlgebraicCurve_PlaceAlgEquiv
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T17:59:51.398123+00:00
-- url     : https://prove2.me/theorems/fb1868b3-f76f-4b23-b705-1b0cc7874ad8
-- title:
--   Transporting places through a field equivalence
-- statement:
--   For a coefficient-preserving field equivalence $e:F≃_k G$, the file defines the induced equivalence from a valuation ring $A⊂F$ to its transported valuation ring in $G$, the transported place $e_*P$, and the residue-algebra equivalence $$κ(P)≃_k κ(e_*P).$$ These objects provide the pointwise transport of valuation and residue data across function-field identifications.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
noncomputable section
namespace AlgebraicCurve.Place

variable {k F G : Type*} [Field k] [Field F] [Field G] [Algebra k F] [Algebra k G]

/-- A field isomorphism identifies a valuation ring with the corresponding
valuation ring on the target field. -/
def mapValuationRingEquiv (e : F ≃ₐ[k] G) (A : ValuationSubring F) :
    A ≃+* A.comap e.symm.toRingHom where
  toFun x := ⟨e x, by change e.symm (e x) ∈ A; simpa using x.property⟩
  invFun y := ⟨e.symm y, y.property⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change e ((x : F) * (y : F)) = e x * e y
    exact e.map_mul x y
  map_add' x y := by
    apply Subtype.ext
    change e ((x : F) + (y : F)) = e x + e y
    exact e.map_add x y

/-- Transport an actual place through a constant-preserving field isomorphism. -/
def mapAlgEquiv (e : F ≃ₐ[k] G) (p : AlgebraicCurve.Place k F) :
    AlgebraicCurve.Place k G where
  toValuationSubring := p.toValuationSubring.comap e.symm.toRingHom
  algebraMap_mem' a := by
    change e.symm (algebraMap k G a) ∈ p.toValuationSubring
    rw [e.symm.commutes]
    exact p.algebraMap_mem' a
  ne_top' h := p.ne_top' (by
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hx : e x ∈ p.toValuationSubring.comap e.symm.toRingHom := by
        rw [h]; trivial
      simpa using hx)
  isPrincipalIdealRing' := IsPrincipalIdealRing.of_surjective
    (mapValuationRingEquiv e p.toValuationSubring)
    (mapValuationRingEquiv e p.toValuationSubring).surjective

/-- The residue algebra is preserved by transport of a place. -/
def mapResidueAlgEquiv (e : F ≃ₐ[k] G) (p : AlgebraicCurve.Place k F) :
    p.ResidueField ≃ₐ[k] (mapAlgEquiv e p).ResidueField :=
  by
    let E : p.toValuationSubring ≃+* (mapAlgEquiv e p).toValuationSubring :=
      mapValuationRingEquiv e p.toValuationSubring
    apply AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv E)
    intro a
    have h : E (algebraMap k p.toValuationSubring a) =
        algebraMap k (mapAlgEquiv e p).toValuationSubring a := by
      apply Subtype.ext
      exact e.commutes a
    show IsLocalRing.ResidueField.mapEquiv E (IsLocalRing.residue _ _) =
      IsLocalRing.residue _ _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    exact congrArg _ h

end AlgebraicCurve.Place


