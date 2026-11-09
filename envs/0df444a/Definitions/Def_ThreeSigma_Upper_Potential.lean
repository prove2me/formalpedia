-- Prove2me | Definitions.Def_ThreeSigma_Upper_Potential
-- name    : ThreeSigma_Upper_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:58.174634+00:00
-- url     : https://prove2.me/theorems/1537d0f2-e25a-4700-9194-3beabbbaa905
-- title:
--   Smooth potential Φ, residual scale s, and open domain 𝒰
-- statement:
--   For arbitrary rows $a_1,\ldots,a_m\in\mathbb R^n$, a real parameter $\Delta$, and $z\in\mathbb R^n$, set
--   $$s(z)=n-\|z\|_2^2-4,\qquad \Phi(z)=\frac1{s(z)}\sum_{i=1}^m\phi\left(\frac{\Delta-\langle a_i,z\rangle}{\sqrt{s(z)}}\right),$$
--   $$\mathcal U=\{z:s(z)>0,\ \langle a_i,z\rangle<\Delta\text{ for every }i\}.$$
--   This is the smooth formula used by Lemma 3.5 for arbitrary rows; it does not impose entry bounds or cube membership.
--
--   **Formalization Note** The formula is a total real function; only its restriction to $\mathcal U$ is used for differentiation. There, $s$ and every scalar argument are strictly positive. This module makes no claim about an extended-valued potential on the boundary of $\mathcal K$.
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), §3, p. 6, equation (3), and §3.3, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Scalar
import Definitions.Def_ThreeSigma_Upper_Geometry

namespace ThreeSigma.Upper

/-- The residual scale in (3), computed by real subtraction. -/
noncomputable def s {n : ℕ} (z : E n) : ℝ := R z - 4

/-- The smooth real formula (3), not the extended potential on the boundary of K.
Only its restriction to U is used in a theorem. Rows may be arbitrary. -/
noncomputable def Phi {m n : ℕ} (a : Fin m → E n) (Δ : ℝ) (z : E n) : ℝ :=
  (s z)⁻¹ * ∑ i, phi ((Δ - inner ℝ (a i) z) / Real.sqrt (s z))

/-- The open domain of the smooth formula (p. 7); no cube constraint. -/
noncomputable def U {m n : ℕ} (a : Fin m → E n) (Δ : ℝ) : Set (E n) :=
  {z | 0 < s z ∧ ∀ i, inner ℝ (a i) z < Δ}

end ThreeSigma.Upper


