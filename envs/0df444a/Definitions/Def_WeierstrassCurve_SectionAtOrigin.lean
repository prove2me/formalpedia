-- Prove2me | Definitions.Def_WeierstrassCurve_SectionAtOrigin
-- name    : WeierstrassCurve_SectionAtOrigin
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/fbec5a9e-2e58-5f27-bcd1-76d41542dd29
-- title:
--   Chart at the origin of a projective Weierstrass model
-- statement:
--   Throughout, $T$ is a commutative ring and $W$ a projective Weierstrass cubic over $T$, with associated graded quotient $R_W = T[X_0,X_1,X_2]/(W.\text{polynomial})$, grading `projModelGradingCR W` induced from the total degree, and $\operatorname{Proj}$ of that grading as the projective model `projModelCR W`. The helper `coord W i` denotes the class of the variable $X_i$ in $R_W$, and `coord_mem` records that this class lies in the degree-one graded piece (the cubic being homogeneous, the ideal is homogeneous, so the grading descends). The chart ring `OriginChartRing W` is Mathlib's degree-zero homogeneous localisation `Away` of the graded ring at the degree-one element `coord W 1`, i.e. the ring of functions on $D_+(X_1)$, the standard affine open containing the origin $[0:1:0]$; `originChartι W` is the corresponding affine open immersion $\operatorname{Spec}$ of that ring into `projModelCR W`. Two distinguished elements of the chart ring are named: `xOverY W` and `zOverY W`, the fractions $X_0/X_1$ and $X_2/X_1$, each written as a numerator of degree one over the first power of `coord W 1`.
--
--   Given a section $P$ of the projective model over $T$ (a morphism from $\operatorname{Spec} T$ to `projModelCR W` compatible with the structure morphism) and a ring homomorphism $\chi$ from the chart ring to $T$, the predicate `IsOriginChartSection P χ` asserts the factorisation $P = \operatorname{Spec}(\chi)$ followed by `originChartι W`; it is a property of the pair $(P,\chi)$, no existence or uniqueness of such a $\chi$ being asserted here. From $\chi$ one reads off two elements of $T$, `originParam χ` $= -\chi(X_0/X_1)$ and `originW χ` $= -\chi(X_2/X_1)$, the classical formal-group coordinates $z=-x/y$ and $w=-1/y$. Finally, for an ideal $I$ of $T$, `ReducesToOrigin P χ I` is the conjunction of `IsOriginChartSection P χ` with $z,w \in I$.
--
--   **Relation to Mathlib.** The chart ring and its immersion into $\operatorname{Proj}$ are Mathlib's `HomogeneousLocalization.Away` and `Proj.awayι` applied to the project's graded quotient by the homogeneous Weierstrass cubic; the section-through-the-chart predicate and the coordinates $z,w$ are the project's own.
--
--   **Where it is used.** These definitions provide the chart through which a $T$-point of the projective Weierstrass model is given affine coordinates near the origin, so that a global level structure can be compared with a formal-group one and the completed local ring of the moduli problem can be compared with a deformation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_SectionAtOrigin.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal

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

abbrev coord (i : Fin 3) : ProjModelRingCR W :=
  Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (X i)

theorem coord_mem (i : Fin 3) : coord W i ∈ projModelGradingCR W 1 :=
  mk_mem_quotGradingSubmodule _ _ (isHomogeneous_X T i)

abbrev OriginChartRing : Type u := Away (projModelGradingCR W) (coord W 1)

abbrev originChartι : Spec (CommRingCat.of (OriginChartRing W)) ⟶ projModelCR W :=
  Proj.awayι (projModelGradingCR W) (coord W 1) (coord_mem W 1) one_pos

def xOverY : OriginChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 1) 1 (coord W 0) (by simpa using coord_mem W 0)

def zOverY : OriginChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 1) 1 (coord W 2) (by simpa using coord_mem W 2)

variable {W}

def IsOriginChartSection (P : Section W) (χ : OriginChartRing W →+* T) : Prop :=
  P.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W

def originParam (χ : OriginChartRing W →+* T) : T := - χ (xOverY W)

def originW (χ : OriginChartRing W →+* T) : T := - χ (zOverY W)

def ReducesToOrigin (P : Section W) (χ : OriginChartRing W →+* T) (I : Ideal T) : Prop :=
  IsOriginChartSection P χ ∧ originParam χ ∈ I ∧ originW χ ∈ I

end WeierstrassCurve.DrinfeldGlobal

end


