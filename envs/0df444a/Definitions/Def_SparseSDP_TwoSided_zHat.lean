-- Prove2me | Definitions.Def_SparseSDP_TwoSided_zHat
-- name    : SparseSDP_TwoSided_zHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:28.343777+00:00
-- url     : https://prove2.me/theorems/fb426902-9126-407a-a4b2-1562bac42662
-- title:
--   The coordinate-sampling estimator $Z_A(\psi,i)$ and its clipped form
-- statement:
--   For a matrix $A$, a vector $\psi$ and a coordinate $i$ in the support of $\psi$,
--   $$
--   Z_A(\psi,i)=\mathrm{Re}\Big\{\frac{[A\psi]_i}{[\psi]_i}\Big\},
--   $$
--   Eq. (77). With $\mathrm{clip}_B(z)=\max\{-B,\min\{z,B\}\}$, the clipped estimator is $\hat Z_{A,B}=\mathrm{clip}_B(RZ_A(\psi,I))$, Eq. (80). One sampled coordinate $I$ serves all constraints at once.
--
--   **Formalization Note** At $[\psi]_i=0$ Lean's $x/0=0$ gives the value $0$. Such $i$ have weight $|[\psi]_i|^2=0$, so no expectation sees it.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Eqs. (77), (80), pp. 22–23

import Mathlib

open Matrix

namespace SparseSDP.TwoSided

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The coordinate-sampling estimator `Z_A(ψ, i) = Re{[Aψ]ᵢ/[ψ]ᵢ}`, Eq. (77), p. 22.

**Formalization Note.** For `[ψ]ᵢ = 0` Lean's `x / 0 = 0` gives `0`; such `i` have sampling weight
`|[ψ]ᵢ|² = 0`, so no statement sees that value. -/
noncomputable def zEst (A : Matrix (Fin n) (Fin n) 𝕜) (ψ : Fin n → 𝕜) (i : Fin n) : ℝ :=
  RCLike.re ((A *ᵥ ψ) i / ψ i)

/-- `clip_B(z) = max{−B, min{z, B}}` (p. 23). -/
noncomputable def clip (B z : ℝ) : ℝ := max (-B) (min z B)

/-- The clipped estimator `Ẑ_{A,B} = clip_B(R Z_A(ψ, I))`, Eq. (80), p. 23, at `I = i`. -/
noncomputable def zHat (A : Matrix (Fin n) (Fin n) 𝕜) (ψ : Fin n → 𝕜) (R B : ℝ) (i : Fin n) : ℝ :=
  clip B (R * zEst A ψ i)

end SparseSDP.TwoSided


