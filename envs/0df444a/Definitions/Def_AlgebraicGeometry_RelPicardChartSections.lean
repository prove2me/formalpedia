-- Prove2me | Definitions.Def_AlgebraicGeometry_RelPicardChartSections
-- name    : AlgebraicGeometry_RelPicardChartSections
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/31d45a2a-5cdf-552b-9bb4-4e1e4b131c7c
-- title:
--   Chart-section conditions on fibres of a relative curve
-- statement:
--   Fix a commutative ring $R$ and a morphism $c \colon C \to \operatorname{Spec} R$. A section of $c$ is an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, i.e. a morphism $\varphi \colon \operatorname{Spec} R \to C$ with $\varphi$ followed by $c$ equal to the identity. For such a $\gamma$ and a morphism $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$ with $k$ a field, `sectionFibrePoint` produces the induced point of the fibre: the morphism $\operatorname{Spec} k \to C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ with components $s$ followed by $\gamma$ and the identity, packaged together with the proof that it is a section of the second projection.
--
--   Given natural numbers $n, g, r$, a family $\gamma_{i j}$ of sections indexed by $i \in \mathrm{Fin}\,n$ and $j \in \mathrm{Fin}\,(r - g)$ (truncated subtraction), an algebraically closed $k$, a geometric point $s$, a field extension $L/k$, a curve model $M$ of $L/k$ (a proper integral scheme, smooth of relative dimension $1$ over $k$, with function field identified with $L$ and closed points identified with the places of $L/k$), and an isomorphism $e \colon M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ compatible with the structure morphisms, the predicate `ChartSectionsAt` is the conjunction of two conditions on divisors of $L/k$ (finitely supported $\mathbb{Z}$-valued functions on places, with degree weighted by residue degrees, and $\ell(D)$ the $k$-dimension of the Riemann–Roch space of $D$):
--
--   (i) there is a divisor $K_c$ with $\ell(D) - \ell(K_c - D) = \deg D + 1 - g$ for every divisor $D$; and
--
--   (ii) for every effective divisor $D$ of degree exactly $r$ there is an index $i$ with $\ell\bigl(D - \sum_{j} P_{i j}\bigr) = 1$, where $P_{i j}$ is the place corresponding under $M.\mathrm{pointEquivPlace}$ to the $k$-point obtained from `sectionFibrePoint` of $\gamma_{i j}$ transported along $e^{-1}$.
--
--   Thus Riemann–Roch with the given genus $g$ is part of the condition, tying $g$ to the curve. `HasChartSections c γ` asserts that for every algebraically closed $k$ and every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$ there exist $L$, a curve model $M$ of $L/k$ and a compatible isomorphism $e$ of $M.C$ with the fibre for which `ChartSectionsAt` holds; the model is existentially quantified, so a provider must exhibit one. `HasChartSectionsOverClosedPoints` imposes the same requirement only for those $s$ whose image of the closed point of $\operatorname{Spec} k$ is a closed point of $\operatorname{Spec} R$.
--
--   **Relation to Mathlib.** Mathlib has no notion of relative Picard charts, of places and divisors of a function field in this sense, or of a curve model; the places, divisors, $\ell$-invariants and `CurveModel` used here are the project's own, built on Mathlib's scheme-theoretic pullbacks, smoothness and properness.
--
--   **Where it is used.** These predicates are the hypotheses under which the relative Jacobian of a curve over a base is constructed in the project: condition (ii) says that the charts indexed by $i$, cut out by $\ell(D - \sum_j P_{ij}) = 1$, cover the degree-$r$ effective divisors on each geometric fibre. The Jacobian so obtained feeds the modular-curve and Néron-model infrastructure used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardChartSections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra AlgebraicCurve

universe u

noncomputable def sectionFibrePoint {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {k : Type u} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    {p : Spec (CommRingCat.of k) ⟶ pullback c s // p ≫ pullback.snd c s = 𝟙 _} :=
  ⟨pullback.lift (s ≫ γ.1) (𝟙 _) (by rw [Category.assoc, γ.2, Category.comp_id, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

def ChartSectionsAt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {n g r : ℕ} (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    {L : Type u} [Field L] [Algebra k L] (M : CurveModel k L)
    (e : M.C ≅ pullback c s) (he : e.hom ≫ pullback.snd c s = M.toBase) : Prop :=
  (∃ Kc : Divisor k L, ∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) ∧
  ∀ D : Divisor k L, (∀ v, 0 ≤ D v) → Divisor.degree D = r →
    ∃ i : Fin n, ell (D - ∑ j : Fin (r - g),
      Finsupp.single (M.pointEquivPlace
        ⟨(sectionFibrePoint (γ i j) s).1 ≫ e.inv, by
          rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (sectionFibrePoint (γ i j) s).2⟩) 1) = 1

def HasChartSections {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {n g r : ℕ} (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (M : CurveModel k L)
      (e : M.C ≅ pullback c s) (he : e.hom ≫ pullback.snd c s = M.toBase), ChartSectionsAt γ s M e he

def HasChartSectionsOverClosedPoints {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {n g r : ℕ} (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
    IsClosed ({s.base (IsLocalRing.closedPoint k)} : Set (Spec (CommRingCat.of R))) →
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (M : CurveModel k L)
      (e : M.C ≅ pullback c s) (he : e.hom ≫ pullback.snd c s = M.toBase), ChartSectionsAt γ s M e he

end AlgebraicGeometry.RelPicard


