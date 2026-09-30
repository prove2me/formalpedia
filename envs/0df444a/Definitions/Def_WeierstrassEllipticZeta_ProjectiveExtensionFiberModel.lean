-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
-- name    : WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-08T17:51:07.009433+00:00
-- url     : https://prove2.me/theorems/77e8ca0d-816b-4664-bdc7-b081758b469a
-- title:
--   Projective additive-fiber model and homogeneous shear
-- statement:
--   Let $g_2,g_3\in\mathbb C$ be arbitrary, and consider the projective locus
--
--   $$Z^\circ_{g_2,g_3}=\{[X_0:X_1:X_2:X_3:X_4]\in\mathbb P^4(\mathbb C):
--   X_0X_4-X_2X_3-2X_1^2=0,\quad
--   X_0X_2^2-4X_1^3+g_2X_0^2X_1+g_3X_0^3=0,\quad
--   X_0\ne0\text{ or }X_2\ne0\}.$$
--
--   A projective additive-fiber model consists of a projection $\pi:Z^\circ_{g_2,g_3}\to\mathbb P^2(\mathbb C)$ and an additive action $A:\mathbb C\times Z^\circ_{g_2,g_3}\to Z^\circ_{g_2,g_3}$ satisfying the following requirements:
--
--   $$\pi([X])=[X_0:X_1:X_2],\qquad
--   A(u,[X])=[X_0:X_1:X_2:X_3+uX_0:X_4+uX_2].$$
--
--   The image of $\pi$ is exactly the homogeneous Weierstrass cubic, written in the coordinate order $(Z,X,Y)$:
--
--   $$\{[Z:X:Y]\in\mathbb P^2(\mathbb C):ZY^2-4X^3+g_2Z^2X+g_3Z^3=0\}.$$
--
--   The action satisfies $A(0,p)=p$ and $A(u+v,p)=A(u,A(v,p))$. It is simply transitive on every fiber:
--
--   $$\pi(p)=\pi(q)\quad\Longleftrightarrow\quad\exists!\,u\in\mathbb C,\ A(u,p)=q.$$
--
--   All formulas are independent of homogeneous representatives and include the fiber at infinity. No discriminant assumption is required for this statement about complex points; it also applies to singular cubic parameters. This supplies the explicit additive-fiber geometry used in the elliptic-extension construction. It does not assert a scheme structure, regularity of morphisms, or a group law on the total space.
--
--   The interface records these maps and laws as data. Its existence is a separate theorem obligation. Auxiliary definitions give the three-coordinate projection, the five-coordinate shear, the homogeneous cubic polynomial, and the forgetful map to the ambient projective space.
-- source:
--   Algebraic consequence of Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, exact sequence (A.3) and the homogeneous, regular and lattice-point exponential-map displays between (A.3) and (A.4), https://doi.org/10.1017/S001309152610145X. Translation of the second elliptic-extension parameter gives the stated shear. The quadric and cubic coordinate relations yield the complete pointwise fiber model. The extension to arbitrary, possibly singular cubic parameters is an inferred algebraic generalization, proved here; no algebraic-group identification is asserted.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus

noncomputable section
namespace WeierstrassEllipticZeta

/-- The first three homogeneous coordinates, in the order `(Z, X, Y)`. -/
def extensionBaseVector (v : Fin 5 → ℂ) : Fin 3 → ℂ := ![v 0, v 1, v 2]

/-- Translation in the additive fiber in homogeneous coordinates. -/
def extensionFiberShear (u : ℂ) (v : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![v 0, v 1, v 2, v 3 + u * v 0, v 4 + u * v 2]

/-- The homogeneous Weierstrass cubic, with coordinates `(Z, X, Y)`. -/
def extensionBaseCubic (g₂ g₃ : ℂ) (v : Fin 3 → ℂ) : ℂ :=
  v 0 * v 2 ^ 2 - 4 * v 1 ^ 3 + g₂ * v 0 ^ 2 * v 1 + g₃ * v 0 ^ 3

/-- Forget the equations and chart condition of a projective point. -/
def extensionProjectivePoint {g₂ g₃ : ℂ} (p : ProjectiveExtensionChartLocus g₂ g₃) :
    Projectivization ℂ (Fin 5 → ℂ) := p.val.val

attribute [local irreducible] ProjectiveExtensionChartLocus ProjectiveExtensionLocus

/-- A pointwise additive-fiber model of the two-chart projective locus.
Its projection has exactly the projective Weierstrass cubic as image. Its
additive action is the displayed homogeneous shear and acts simply transitively
on each fiber. Existence, all action laws, and fiber classification are theorem
obligations; this interface asserts no scheme structure or total-space group law. -/
structure ProjectiveExtensionFiberModel (g₂ g₃ : ℂ) where
  projection : ProjectiveExtensionChartLocus g₂ g₃ → Projectivization ℂ (Fin 3 → ℂ)
  action : ℂ → ProjectiveExtensionChartLocus g₂ g₃ → ProjectiveExtensionChartLocus g₂ g₃
  projection_coords : ∀ p : ProjectiveExtensionChartLocus g₂ g₃,
    ∃ hv : extensionBaseVector (extensionProjectivePoint p).rep ≠ 0,
    projection p = Projectivization.mk ℂ (extensionBaseVector (extensionProjectivePoint p).rep) hv
  projection_cubic : ∀ p : ProjectiveExtensionChartLocus g₂ g₃, extensionBaseCubic g₂ g₃ (projection p).rep = 0
  projection_surjective : ∀ b : Projectivization ℂ (Fin 3 → ℂ),
    extensionBaseCubic g₂ g₃ b.rep = 0 → ∃ p, projection p = b
  action_coords : ∀ (u : ℂ) (p : ProjectiveExtensionChartLocus g₂ g₃),
    ∃ hv : extensionFiberShear u (extensionProjectivePoint p).rep ≠ 0,
    extensionProjectivePoint (action u p) =
      Projectivization.mk ℂ (extensionFiberShear u (extensionProjectivePoint p).rep) hv
  zero_action : ∀ p : ProjectiveExtensionChartLocus g₂ g₃, action 0 p = p
  add_action : ∀ (u v : ℂ) (p : ProjectiveExtensionChartLocus g₂ g₃), action (u + v) p = action u (action v p)
  fiber : ∀ p q : ProjectiveExtensionChartLocus g₂ g₃, projection p = projection q ↔ ∃! u : ℂ, action u p = q

end WeierstrassEllipticZeta


