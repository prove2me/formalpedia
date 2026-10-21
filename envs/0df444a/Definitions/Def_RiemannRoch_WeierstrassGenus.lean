-- Prove2me | Definitions.Def_RiemannRoch_WeierstrassGenus
-- name    : RiemannRoch_WeierstrassGenus
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T13:35:10.68544+00:00
-- url     : https://prove2.me/theorems/c2bffde8-f251-4e2e-86a7-b1c5531cdfc0
-- title:
--   Places of points of an elliptic curve as places of its function field, and degree-one places
-- statement:
--   Let $k$ be a field and $W$ an elliptic Weierstrass curve over $k$, $y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6$ with nonzero discriminant, let $K$ be a fraction field of its coordinate ring $k[W]$ with compatible embeddings $k\subset k[X]\subset k[W]$, $k[X]\subset k(X)\subset K$, such that $K/k(X)$ is finite separable and $k$ is the full constant field of $K$. Let $\mathbb P^{\mathrm{ch}}_K$ be the chart places, $\infty\in\mathbb P^{\mathrm{ch}}_K$ the place at infinity and $P\mapsto\mathfrak p^{\mathrm{ch}}_P$ the point–place map $W(k)\to\mathbb P^{\mathrm{ch}}_K$ (file `RiemannRoch_WeierstrassInfinity`), and let $Q\mapsto Q^{\mathrm{int}}$ be the bijection from chart places to intrinsic places of $K/k$ (valuation subrings $\mathcal O\subsetneq K$ containing $k$ with value group $\cong\mathbb Z$).
--
--   This file introduces:
--
--   1. the chart divisor $1\cdot\infty$;
--   2. the **intrinsic place at infinity** $\infty^{\mathrm{int}}$ and, for every point $P\in W(k)$, the **intrinsic place of $P$**, $\mathfrak p_P=(\mathfrak p^{\mathrm{ch}}_P)^{\mathrm{int}}$, so that $\mathfrak p_O=\infty^{\mathrm{int}}$;
--   3. the bijection
--   $$\{\text{places }v\text{ of }K/k:\ \deg v=1\}\ \xrightarrow{\ \sim\ }\ \{Q\in\mathbb P^{\mathrm{ch}}_K:\ \deg Q=1\}$$
--   induced by the chart–intrinsic bijection.
--
--   It also contains the structural lemma $y\ne0$ in $K$.
--
--   These are the objects in which the theorems on Weierstrass function fields are stated: the places $\mathfrak p_P$ have degree one, every degree-one place is some $\mathfrak p_P$, and the genus of $K$ is one. In the chain of definition files it imports `RiemannRoch_WeierstrassInfinity` and is imported by `WeilConjectures_RiemannRochFLT`.
--
--   **Formalization Note** The curve is `W : WeierstrassCurve.Affine k` with `[W.IsElliptic]`; the field $K$ carries `[Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]`, `Algebra k[X] K`, `IsScalarTower k[X] W.CoordinateRing K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, `FunctionField k K`, `Algebra.IsSeparable k⟮X⟯ K`, `Algebra k K`, `IsScalarTower k k[X] K` and `IsFullConstantField k K`. The divisor is `Chart.infinityDivisor`, the intrinsic places are `WeierstrassCurve.Affine.infinityPlace K` and `placeOfPoint W K P : Place k K` (images under `chartToPlace`), and the bijection is `degreeOnePlaceEquivChart`, where `Place.degree` and `placeDegree` agree through `placeDegree_eq`. The source modules `GenusCounting`, `GenusOne` and `DegreeOneDictionary` contribute only these few declarations; their theorems are published separately or omitted.
-- source:
--   J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009, III.1 and III.3 (points of an elliptic curve, cf.); H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 6.1 (elliptic function fields, cf.) and Section 1.1 (degree of a place); the place dictionary is an auxiliary construction of the formalization. Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/EllipticCurve/GenusCounting.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/EllipticCurve/GenusOne.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/EllipticCurve/DegreeOneDictionary.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/CoordinateFree/EllipticCurve.lean

import Mathlib
import Definitions.Def_RiemannRoch_WeierstrassInfinity

/-
Contains code from riemann-roch-function-fields
(https://github.com/vaca22/riemann-roch-function-fields, commit dbca5bee),
Copyright (c) 2026 Guanghao Li, released under the Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Modified: ported to Lean v4.33.1 / Mathlib 0df444a (module headers converted, some proofs
adapted to this Mathlib, a few names qualified, `picTorsor` omitted; statements unchanged), then
split into prove2.me definitions and theorems, with comments removed.
-/

set_option linter.style.haveILetI false

section
section
open FunctionField
open FunctionField.Chart
open scoped Polynomial RatFunc WithZero
namespace WeierstrassCurve.Affine.Chart
noncomputable section
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]
omit [WeierstrassCurve.IsElliptic W] [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
lemma yCoord_ne_zero : W.yCoord K ≠ 0 := by
  intro h
  exact W.yCoord_notMem_range K ⟨0, by simpa using h.symm⟩
noncomputable def infinityDivisor : DivisorA k K :=
  Finsupp.single (infinityPlace K) 1
end
end WeierstrassCurve.Affine.Chart
end
end

section
section
open FunctionField
open FunctionField.Chart
open scoped Polynomial RatFunc nonZeroDivisors
namespace WeierstrassCurve.Affine
noncomputable section
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]
noncomputable def infinityPlace : Place k K :=
  chartToPlace k K (Chart.infinityPlace K)
noncomputable def placeOfPoint (P : W.Point) : Place k K :=
  chartToPlace k K (Chart.placeOfPoint W K P)
noncomputable def degreeOnePlaceEquivChart :
    {v : Place k K // v.degree = 1} ≃ {w : PlaceA k K // placeDegree k K w = 1} where
  toFun v := ⟨(chartToPlace k K).symm v.1, by
    rw [placeDegree_eq]
    simpa using v.2⟩
  invFun w := ⟨chartToPlace k K w.1, by
    rw [← placeDegree_eq]
    exact w.2⟩
  left_inv v := Subtype.ext ((chartToPlace k K).apply_symm_apply v.1)
  right_inv w := Subtype.ext ((chartToPlace k K).symm_apply_apply w.1)
end
end WeierstrassCurve.Affine
end
end


