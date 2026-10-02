-- Prove2me | Definitions.Def_HunterPDE_Elliptic_Fredholm
-- name    : HunterPDE_Elliptic_Fredholm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:44:10.424479+00:00
-- url     : https://prove2.me/theorems/3aae8585-4ca6-4411-8ad2-217468dffba9
-- title:
--   Fredholm operators and their index on a Hilbert space (Definitions 4.38–4.39)
-- statement:
--   Let $\mathcal{H}$ be a Hilbert space. A bounded linear operator $T \in \mathcal{L}(\mathcal{H})$ is **Fredholm** (Definition 4.38) if (a) $\ker T$ is finite-dimensional, and (b) $\operatorname{ran} T$ is closed and has finite codimension, where
--   $$\operatorname{codim}\operatorname{ran} T = \dim(\operatorname{ran} T)^\perp .$$
--   The **index** of a Fredholm operator (Definition 4.39) is the integer $\operatorname{ind} T = \dim\ker T - \operatorname{codim}\operatorname{ran} T$.
--
--   **Formalization Note.** The scalar field is any `RCLike` field ($\mathbb{R}$ or $\mathbb{C}$). `index T` is defined for every $T$ with `Module.finrank` (which is $0$ on an infinite-dimensional space), and is only used together with `IsFredholm T`, where both dimensions are finite.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 122, Definitions 4.38–4.39

import Mathlib

namespace HunterPDE.Elliptic

/-- Fredholm operator (Hunter, Definition 4.38): a bounded linear operator `T` on a Hilbert space
`H` is Fredholm if (a) `ker T` is finite-dimensional and (b) `ran T` is closed and has finite
codimension, where `codim ran T = dim (ran T)^⊥`. -/
def IsFredholm {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (T : H →L[𝕜] H) : Prop :=
  FiniteDimensional 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) ∧
    IsClosed (LinearMap.range (T : H →ₗ[𝕜] H) : Set H) ∧
    FiniteDimensional 𝕜 (LinearMap.range (T : H →ₗ[𝕜] H))ᗮ

/-- The index of a Fredholm operator (Definition 4.39):
`ind T = dim ker T − codim ran T = dim ker T − dim (ran T)^⊥`, an integer. (Meaningful when
`IsFredholm T`; both dimensions are then finite.) -/
noncomputable def index {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (T : H →L[𝕜] H) : ℤ :=
  (Module.finrank 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) : ℤ) -
    (Module.finrank 𝕜 (LinearMap.range (T : H →ₗ[𝕜] H))ᗮ : ℤ)

end HunterPDE.Elliptic


