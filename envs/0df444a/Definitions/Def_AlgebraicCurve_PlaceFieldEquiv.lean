-- Prove2me | Definitions.Def_AlgebraicCurve_PlaceFieldEquiv
-- name    : AlgebraicCurve_PlaceFieldEquiv
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:48.105936+00:00
-- url     : https://prove2.me/theorems/ad73ee7e-7dd4-48e7-9581-d7e6e2993e8c
-- title:
--   Equivalences of complete and degree-one place carriers
-- statement:
--   A $k$-algebra equivalence $F≃_k G$ is packaged as an equivalence of all places $$Place_k(F)≃Place_k(G).$$ The transport preserves residue degree and the exact image of every centered subring, and it restricts to an equivalence between the degree-one place carriers. This is the counting-level interface used when two explicit models have isomorphic function fields.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_AlgebraicCurve_PlaceAlgEquiv
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
/-! Places and degree-one places transported through a coefficient-preserving field equivalence. -/
noncomputable section
namespace AlgebraicCurve.Place

variable {k F G : Type*} [Field k] [Field F] [Field G] [Algebra k F] [Algebra k G]

/-- A coefficient-preserving field equivalence identifies the complete place carriers. -/
def algEquiv (e : F ≃ₐ[k] G) : AlgebraicCurve.Place k F ≃ AlgebraicCurve.Place k G where
  toFun := mapAlgEquiv e
  invFun := mapAlgEquiv e.symm
  left_inv p := by
    apply AlgebraicCurve.Place.ext
    ext x
    change e.symm (e x) ∈ p.toValuationSubring ↔ x ∈ p.toValuationSubring
    rw [e.symm_apply_apply]
  right_inv p := by
    apply AlgebraicCurve.Place.ext
    ext x
    change e (e.symm x) ∈ p.toValuationSubring ↔ x ∈ p.toValuationSubring
    rw [e.apply_symm_apply]

/-- The transported residue algebra has the same degree over the coefficient field. -/
theorem mapAlgEquiv_degree (e : F ≃ₐ[k] G) (p : AlgebraicCurve.Place k F) :
    (mapAlgEquiv e p).deg = p.deg :=
  (mapResidueAlgEquiv e p).toLinearEquiv.finrank_eq.symm

/-- Transporting a centered subring preserves its exact inclusion in the target field. -/
theorem mapAlgEquiv_range {A : Type*} [CommRing A]
    (e : F ≃ₐ[k] G) (f : A →+* F) (p : AlgebraicCurve.Place k F)
    (hf : f.range = p.toValuationSubring.toSubring) :
    (e.toRingHom.comp f).range = (mapAlgEquiv e p).toValuationSubring.toSubring := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change e.symm (e (f a)) ∈ p.toValuationSubring
    rw [e.symm_apply_apply]
    change f a ∈ p.toValuationSubring.toSubring
    rw [← hf]
    exact ⟨a, rfl⟩
  · intro hx
    change e.symm x ∈ p.toValuationSubring at hx
    have hmem : e.symm x ∈ f.range := by
      rw [hf]
      exact hx
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, ?_⟩
    change e (f a) = x
    rw [ha, e.apply_symm_apply]

/-- Restrict field transport to the full degree-one place carriers. -/
def degreeOneAlgEquiv (e : F ≃ₐ[k] G) :
    {p : AlgebraicCurve.Place k F // p.deg = 1} ≃
      {p : AlgebraicCurve.Place k G // p.deg = 1} where
  toFun p := ⟨mapAlgEquiv e p.val, (mapAlgEquiv_degree e p.val).trans p.property⟩
  invFun p := ⟨mapAlgEquiv e.symm p.val, (mapAlgEquiv_degree e.symm p.val).trans p.property⟩
  left_inv p := Subtype.ext ((algEquiv e).left_inv p.val)
  right_inv p := Subtype.ext ((algEquiv e).right_inv p.val)

end AlgebraicCurve.Place


