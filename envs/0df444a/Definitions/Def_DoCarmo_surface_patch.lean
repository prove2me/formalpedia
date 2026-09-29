-- Prove2me | Definitions.Def_DoCarmo_surface_patch
-- name    : DoCarmo_surface_patch
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T00:58:14.932095+00:00
-- url     : https://prove2.me/theorems/10fbd366-b3cd-4254-9af1-3abf9a6ac41f
-- title:
--   Regular patch, fundamental forms, Gaussian curvature and Christoffel symbols
-- statement:
--   The local vocabulary for surfaces in do Carmo's Chapters 2-4, in the setting of a single parametrization.
--
--   A **regular parametrized patch** on an open set $U \subseteq \mathbb{R}^2$ is a smooth map $x(u,v)$ into $\mathbb{R}^3$ with $x_u \wedge x_v \neq 0$ on $U$; its **unit normal** is $N = (x_u \wedge x_v)/|x_u \wedge x_v|$ (do Carmo §2-2, §3-2).
--
--   The **first fundamental form** is recorded by $E = \langle x_u,x_u\rangle$, $F = \langle x_u,x_v\rangle$, $G = \langle x_v,x_v\rangle$ (§2-5), and the **second fundamental form** by $e = \langle N,x_{uu}\rangle$, $f = \langle N,x_{uv}\rangle$, $g = \langle N,x_{vv}\rangle$ (§3-3). The **Gaussian curvature** is $K = (eg-f^2)/(EG-F^2)$ (§3-3).
--
--   Finally, the **Christoffel symbols** of the patch are characterized, as in do Carmo's system (1) of §4-3, by the decomposition of the second derivatives of $x$ in the basis $\{x_u, x_v, N\}$:
--
--   $$ x_{uu} = \Gamma^1_{11}x_u + \Gamma^2_{11}x_v + eN, \quad x_{uv} = \Gamma^1_{12}x_u + \Gamma^2_{12}x_v + fN, \quad x_{vv} = \Gamma^1_{22}x_u + \Gamma^2_{22}x_v + gN. $$
--
--   Patches are written in curried form, so that the partial derivatives are ordinary one-variable derivatives; all quantities are total functions of the parameters and the statements of the mission restrict them to the open set $U$.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Sections 2-2, 2-5, 3-3 and 4-3 (pp. 54, 94-96, 155-158, 235-236)

import Definitions.Def_DoCarmo_vector_product

namespace DoCarmoDG

/-- The partial derivative `x_u` of a parametrized patch `x : ℝ → ℝ → ℝ³`,
written in curried form so that partial derivatives are ordinary derivatives. -/
noncomputable def partialU (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  deriv (fun t => x t v) u

/-- The partial derivative `x_v` of a parametrized patch `x : ℝ → ℝ → ℝ³`. -/
noncomputable def partialV (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  deriv (fun t => x u t) v

/-- A regular parametrized patch on an open set `U ⊆ ℝ²`: `x` is smooth on `U` and
`x_u ∧ x_v ≠ 0` there, i.e. `dx` is injective (do Carmo §2-2). -/
def IsRegularPatch (U : Set (ℝ × ℝ)) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry x) U ∧
    ∀ p ∈ U, cross (partialU x p.1 p.2) (partialV x p.1 p.2) ≠ 0

/-- The unit normal `N = (x_u ∧ x_v)/|x_u ∧ x_v|` of a patch (do Carmo §2-6, §3-2). -/
noncomputable def unitNormal (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  ‖cross (partialU x u v) (partialV x u v)‖⁻¹ • cross (partialU x u v) (partialV x u v)

/-- The coefficient `E = ⟨x_u, x_u⟩` of the first fundamental form (do Carmo §2-5). -/
noncomputable def coeffE (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) : ℝ :=
  inner ℝ (partialU x u v) (partialU x u v)

/-- The coefficient `F = ⟨x_u, x_v⟩` of the first fundamental form (do Carmo §2-5). -/
noncomputable def coeffF (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) : ℝ :=
  inner ℝ (partialU x u v) (partialV x u v)

/-- The coefficient `G = ⟨x_v, x_v⟩` of the first fundamental form (do Carmo §2-5). -/
noncomputable def coeffG (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) : ℝ :=
  inner ℝ (partialV x u v) (partialV x u v)

/-- The coefficient `e = ⟨N, x_uu⟩` of the second fundamental form (do Carmo §3-3). -/
noncomputable def coeffe (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) : ℝ :=
  inner ℝ (unitNormal x u v) (partialU (partialU x) u v)

/-- The coefficient `f = ⟨N, x_uv⟩` of the second fundamental form (do Carmo §3-3). -/
noncomputable def coefff (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) : ℝ :=
  inner ℝ (unitNormal x u v) (partialV (partialU x) u v)

/-- The coefficient `g = ⟨N, x_vv⟩` of the second fundamental form (do Carmo §3-3). -/
noncomputable def coeffg (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) : ℝ :=
  inner ℝ (unitNormal x u v) (partialV (partialV x) u v)

/-- The Gaussian curvature `K = (eg - f²)/(EG - F²)` of a patch (do Carmo §3-3). -/
noncomputable def gaussCurvature (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) : ℝ :=
  (coeffe x u v * coeffg x u v - coefff x u v ^ 2) /
    (coeffE x u v * coeffG x u v - coeffF x u v ^ 2)

/-- The Christoffel symbols of `x` in the parametrization, characterized by do Carmo's
equations (1) of §4-3: the second partial derivatives of `x`, decomposed in the basis
`{x_u, x_v, N}`, have tangential coefficients `Γᵏᵢⱼ` and normal coefficients `e, f, g`. -/
def IsChristoffel (U : Set (ℝ × ℝ)) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ) : Prop :=
  ∀ p ∈ U,
    partialU (partialU x) p.1 p.2 =
        G111 p.1 p.2 • partialU x p.1 p.2 + G211 p.1 p.2 • partialV x p.1 p.2 +
          coeffe x p.1 p.2 • unitNormal x p.1 p.2 ∧
      partialV (partialU x) p.1 p.2 =
        G112 p.1 p.2 • partialU x p.1 p.2 + G212 p.1 p.2 • partialV x p.1 p.2 +
          coefff x p.1 p.2 • unitNormal x p.1 p.2 ∧
      partialV (partialV x) p.1 p.2 =
        G122 p.1 p.2 • partialU x p.1 p.2 + G222 p.1 p.2 • partialV x p.1 p.2 +
          coeffg x p.1 p.2 • unitNormal x p.1 p.2

end DoCarmoDG


