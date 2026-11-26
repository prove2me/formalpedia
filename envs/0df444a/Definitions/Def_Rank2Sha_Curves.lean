-- Prove2me | Definitions.Def_Rank2Sha_Curves
-- name    : Rank2Sha_Curves
-- status  : Definition
-- author  : @barindersbanwait
-- created : 2026-11-25T01:06:58.168127+00:00
-- url     : https://prove2.me/theorems/4fd07909-3f1d-479f-ac8f-fed040fcae11
-- title:
--   Two elliptic curves over $\mathbb{Q}$ of rank $2$
-- statement:
--   This file defines two elliptic curves over $\mathbb{Q}$ by their Weierstrass equations.
--
--   1. `curve389a1` is
--
--   $$
--   E_{389} : \; y^2 + y = x^3 + x^2 - 2x ,
--   $$
--
--   with LMFDB label 389.a1 and Cremona label 389a1. Its discriminant is $389$.
--
--   2. `curve56` is
--
--   $$
--   E_{56} : \; y^2 = x^3 - 56x ,
--   $$
--
--   with LMFDB label 12544.g1 and Cremona label 12544b2. Its discriminant is $11239424 = 2^{15} \cdot 7^3$. It has complex multiplication by $\mathbb{Z}[i]$.
--
--   The file proves the two discriminant values and registers both curves as elliptic curves. According to the LMFDB both curves have Mordell–Weil rank $2$; that is not asserted in this file.
--
--   **Formalization Note** A Weierstrass curve is given by its coefficients $(a_1, a_2, a_3, a_4, a_6)$ in $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$; the two curves are $(0,1,1,-2,0)$ and $(0,0,0,-56,0)$.
-- source:
--   https://www.lmfdb.org/EllipticCurve/Q/389/a/1 ; https://www.lmfdb.org/EllipticCurve/Q/12544/g/1

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Two elliptic curves over `ℚ` of rank 2

A `WeierstrassCurve` is given by its coefficients `⟨a₁, a₂, a₃, a₄, a₆⟩`, for the
equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`.
-/

namespace Rank2Sha

/-- The curve `y² + y = x³ + x² - 2x` over `ℚ`, LMFDB label 389.a1, Cremona label 389a1. -/
def curve389a1 : WeierstrassCurve.Affine ℚ := ⟨0, 1, 1, -2, 0⟩

/-- The curve `y² = x³ - 56x` over `ℚ`, LMFDB label 12544.g1, Cremona label 12544b2. -/
def curve56 : WeierstrassCurve.Affine ℚ := ⟨0, 0, 0, -56, 0⟩

/-- The discriminant of `y² + y = x³ + x² - 2x` is `389`. -/
theorem Δ_curve389a1 : curve389a1.Δ = 389 := by
  simp only [curve389a1, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

/-- The discriminant of `y² = x³ - 56x` is `11239424 = 2¹⁵ · 7³`. -/
theorem Δ_curve56 : curve56.Δ = 11239424 := by
  simp only [curve56, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

/-- `y² + y = x³ + x² - 2x` is an elliptic curve over `ℚ`. -/
instance instIsEllipticCurve389a1 : curve389a1.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, Δ_curve389a1]
  exact IsUnit.mk0 _ (by norm_num)

/-- `y² = x³ - 56x` is an elliptic curve over `ℚ`. -/
instance instIsEllipticCurve56 : curve56.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, Δ_curve56]
  exact IsUnit.mk0 _ (by norm_num)

end Rank2Sha


