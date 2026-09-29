-- Prove2me | Definitions.Def_AlgebraicCurve_PlacesOf
-- name    : AlgebraicCurve_PlacesOf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/dbd28932-e6a2-5b3a-bc5e-55873854ffd7
-- title:
--   Places of the function field centred in an open subscheme
-- statement:
--   Throughout, $K$ is a field and $C$ an integral scheme equipped with a morphism $c\colon C \to \operatorname{Spec} K$; the function field $C.\mathrm{functionField}$, i.e. the stalk of $\mathcal O_C$ at the generic point, is regarded as a $K$-algebra via the ring homomorphism [`AlgebraicCurve.baseToFunctionField c`](../def/AlgebraicCurve_CurveModel.html#L18) (the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism, followed by the map on global sections induced by $c$, followed by the germ at the generic point). Recall that an element of [`AlgebraicCurve.Place K F`](../def/AlgebraicCurve_DivisorClassGroup.html#L22) is a valuation subring $\mathcal O_v \subseteq F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring (hence a discrete valuation ring).
--
--   For an open subscheme $U$ of $C$, [`AlgebraicCurve.placesOf c U`](../def/AlgebraicCurve_PlacesOf.html#L17) is defined to be the set of places $v$ of $K(C)/K$ that admit a centre in $U$: those $v$ for which there is a point $x \in U$ whose singleton $\{x\}$ is closed in $C$ and such that the image of the canonical map $\mathcal O_{C,x} \to K(C)$, taken as a subring of $K(C)$, is exactly $\mathcal O_v$. This is a definition of vocabulary only: no regularity, properness or smoothness is assumed, and nothing is asserted about existence or uniqueness of such a centre.
--
--   The accompanying lemmas record the elementary behaviour of this set as a function of $U$: `mem_placesOf_iff` restates membership in the above existential form; `placesOf_mono` gives $U \le V \Rightarrow \mathtt{placesOf}\,c\,U \subseteq \mathtt{placesOf}\,c\,V$; `placesOf_sup` gives $\mathtt{placesOf}\,c\,(U \sqcup V) = \mathtt{placesOf}\,c\,U \cup \mathtt{placesOf}\,c\,V$, since a centre lying in the union of two opens lies in one of them; and `placesOf_bot` gives $\mathtt{placesOf}\,c\,\bot = \varnothing$. Compatibility with intersections, and surjectivity onto all places for $U = C$, are not formal consequences of the definition and belong to the theory of smooth proper curves.
--
--   **Relation to Mathlib.** Built on Mathlib's `Scheme.functionField` and stalk machinery, but the notion of a place of $F/K$ used here is the project's own structure [`AlgebraicCurve.Place`](../def/AlgebraicCurve_DivisorClassGroup.html#L22) (a valuation subring of $F$ over $K$, proper and a principal ideal ring), and Mathlib has no notion of the set of places centred in a given open subscheme.
--
--   **Where it is used.** This vocabulary lets statements about a curve over $K$ be phrased simultaneously in scheme-theoretic and function-field terms: sections of $\mathcal O_C$ over an affine open are compared with the intersection of the valuation rings $\mathcal O_v$ for $v$ centred in that open, and Čech computations for a cover by two affine opens are matched with their function-field counterparts. Such comparisons feed the divisor and Jacobian theory of curves used in the arithmetic input to the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_PlacesOf.lean

import Mathlib.AlgebraicGeometry.FunctionField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]

def placesOf (U : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    Set (Place K C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  {v | ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
    (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring}

theorem mem_placesOf_iff (U : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, v ∈ placesOf c U ↔ ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring :=
  fun _ => Iff.rfl

theorem placesOf_mono {U V : C.Opens} (h : U ≤ V) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c U ⊆ placesOf c V := by
  rintro v ⟨x, hxU, hx, hv⟩
  exact ⟨x, h hxU, hx, hv⟩

theorem placesOf_sup (U V : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (U ⊔ V) = placesOf c U ∪ placesOf c V := by
  letI := (baseToFunctionField c).toAlgebra
  apply Set.Subset.antisymm
  · rintro v ⟨x, hxUV, hx, hv⟩
    rcases (show x ∈ (U : Set C) ∪ (V : Set C) from hxUV) with h | h
    · exact Or.inl ⟨x, h, hx, hv⟩
    · exact Or.inr ⟨x, h, hx, hv⟩
  · rintro v (h | h)
    · exact placesOf_mono c le_sup_left h
    · exact placesOf_mono c le_sup_right h

theorem placesOf_bot :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (⊥ : C.Opens) = ∅ := by
  letI := (baseToFunctionField c).toAlgebra
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, hx, -, -⟩
  exact hx

end AlgebraicCurve

end


