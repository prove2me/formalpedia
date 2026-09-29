-- Prove2me | Definitions.Def_WeierstrassCurve_PointChart
-- name    : WeierstrassCurve_PointChart
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/4687eea3-0fda-579b-90b6-b0d567b01fec
-- title:
--   Finite chart D+​(Z) and sections through affine points
-- statement:
--   Throughout, $T$ is a commutative ring and $W$ a projective Weierstrass curve over $T$; the projective model is $E = \mathrm{Proj}$ of the graded ring $\mathcal{A} = T[X_0,X_1,X_2]/(W_{\mathrm{hom}})$, with grading induced from the total-degree grading of the polynomial ring, and $\mathrm{coord}\,W\,i$ denotes the class of $X_i$, an element of degree $1$. `ZChartRing W` is the degree-zero part of the homogeneous localisation of $\mathcal{A}$ away from $\mathrm{coord}\,W\,2$, and `zChartι` is the associated open immersion $\mathrm{Spec}(\mathrm{ZChartRing}\,W) \to E$ onto the standard chart $D_+(Z)$, obtained from Mathlib's `Proj.awayι` at the degree-one element $\mathrm{coord}\,W\,2$. The two elements `xOverZ` and `yOverZ` of this ring are the degree-zero fractions with numerators $\mathrm{coord}\,W\,0$ and $\mathrm{coord}\,W\,1$ over the first power of $\mathrm{coord}\,W\,2$, i.e. the affine coordinates $x = X/Z$ and $y = Y/Z$ of the chart.
--
--   For a section $S$ of $E$ over $T$ (an element of `Section W`, a morphism $\mathrm{Spec}\,T \to E$ whose composite with the structure morphism is the identity) and a ring homomorphism $\chi$ from `ZChartRing W` to $T$, the predicate `IsZChartSection S χ` asserts the equality of morphisms $S.1 = \mathrm{Spec}(\chi)$ followed by `zChartι`: the section factors through the chart $D_+(Z)$ via $\chi$. The coordinates of such a factorisation are $\mathrm{affX}\,\chi = \chi(x)$ and $\mathrm{affY}\,\chi = \chi(y)$. Finally, `IsSectionThrough S x y`, for $x, y \in T$, asserts the existence of a $\chi$ with `IsZChartSection S χ` and $\chi(x\text{-coordinate}) = x$, $\chi(y\text{-coordinate}) = y$. All three are predicates on the given section and the chosen homogeneous presentation of the model; nothing is constructed or proved here.
--
--   **Relation to Mathlib.** Mathlib supplies the homogeneous localisation `Away` and the open immersion `Proj.awayι` used here; the projective Weierstrass model as $\mathrm{Proj}$ of a graded quotient, its charts and the predicate that a section passes through a given affine point are the project's own notions, with no Mathlib counterpart.
--
--   **Where it is used.** These predicates provide the language in which a $T$-section of the projective Weierstrass model is said to have affine coordinates $(x,y)$; the companion module for the chart $D_+(Y)$ treats sections near the origin $[0:1:0]$. They are used when the Drinfeld level structures and the relative group law on the model are read in coordinates, in particular when comparing the group law on field-valued points with the chord–tangent addition on the affine Weierstrass curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_PointChart.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel MvPolynomial HomogeneousLocalization
open HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.DrinfeldGlobal

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

abbrev ZChartRing : Type u := Away (projModelGradingCR W) (coord W 2)

abbrev zChartι : Spec (CommRingCat.of (ZChartRing W)) ⟶ projModelCR W :=
  Proj.awayι (projModelGradingCR W) (coord W 2) (coord_mem W 2) one_pos

def xOverZ : ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 0) (by simpa using coord_mem W 0)

def yOverZ : ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 1) (by simpa using coord_mem W 1)

variable {W}

def IsZChartSection (S : Section W) (χ : ZChartRing W →+* T) : Prop :=
  S.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W

def affX (χ : ZChartRing W →+* T) : T := χ (xOverZ W)

def affY (χ : ZChartRing W →+* T) : T := χ (yOverZ W)

def IsSectionThrough (S : Section W) (x y : T) : Prop :=
  ∃ χ : ZChartRing W →+* T, IsZChartSection S χ ∧ affX χ = x ∧ affY χ = y

end WeierstrassCurve.DrinfeldGlobal

end


