-- Prove2me | Definitions.Def_TorusEuler_Affine
-- name    : TorusEuler_Affine
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T19:38:06.641203+00:00
-- url     : https://prove2.me/theorems/e8593b87-39e6-44db-81e4-4a1d5f99561b
-- title:
--   Affine plane waves, moving frame, and the wave ODEs
-- statement:
--   The affine-wave machinery of Lemmas 2.1–2.2. For a matrix $D$ and a wave vector $k\ne0$, the **amplitude operator** is
--   $$A(D,k) = -D + \frac{2}{\|k\|^2}\,(k\otimes k)\,D,$$
--   the projection-corrected background acting on amplitudes. Given a scalar profile $F$, a background $D(t)$, a wave vector $k(t)$ and an amplitude $a(t)$, the **affine wave velocity** is $u(t,x)=D(t)x + F(k(t)\cdot x)\,a(t)$; the **wave pressure coefficient** is $p_{\mathrm w}=2k\cdot Da/\|k\|^2$; and with $S=D'+D^2$ the **wave pressure** is $-\tfrac12 x\cdot Sx - p_{\mathrm w}P(k\cdot x)$, where $P'=F$. `cross3` is the oriented cross product on $\mathbb{R}^3$.
--
--   The **moving frame** of a wave (`frame`) is $E_1=k/\|k\|$, $E_2=a/\|a\|$, $E_3=E_1\times E_2$; `entry e B i j` is the matrix entry $E_i\cdot B E_j$ (zero-based indices). `WaveOn J D k a` asserts the two Craik–Criminale ODEs on the interval $J$, derivatives taken within $J$:
--   $$k' = -D^{\mathsf T}k,\qquad a' = A(D,k)\,a = -Da + \frac{2k\cdot Da}{\|k\|^2}\,k.$$
--
--   **Formalization Note** The pressure coefficient $p_{\mathrm w}$ is substituted into the amplitude equation in `WaveOn`; transversality $k\cdot a=0$ is stated separately where needed (it is preserved by the flow, Lemma 2.1).
-- source:
--   Alpöge–Buckmaster–Coiculescu, *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, frozen manuscript of 18 November 2026 (torus-paper-freeze-2026-11-18). Lean: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/formalization/lean/TorusEuler/ (AffinePropagation.lean#L12, ExactAffineEuler.lean#L24-L35, CurlProjection.lean, MovingCoordinateWaveVector.lean#L13-L17, PaperAffineStatements.lean#L18-L22); TeX: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/frozen-manuscript/sections/02_affine.tex (cc:eq:wave-ode).

import Mathlib
import Definitions.Def_TorusEuler_Statement

open scoped InnerProductSpace

noncomputable section

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear amplitude operator for a prescribed wave vector. -/
noncomputable def affineWaveAmplitudeOperator (D : E →L[ℝ] E) (k : E) : E →L[ℝ] E :=
  -D + (2 / ‖k‖ ^ 2) • (InnerProductSpace.rankOne ℝ k k).comp D

/-- The affine velocity plus one plane wave in Lemma 2.1 (cc:lem:wave). -/
noncomputable def affineWaveVelocity (F : ℝ → ℝ) (D : ℝ → Vec3 →L[ℝ] Vec3) (k a : ℝ → Vec3) :
    Velocity :=
  fun t x => D t x + F ⟪k t, x⟫_ℝ • a t

/-- The coefficient of the wave pressure in (cc:eq:wave-ode). -/
noncomputable def affineWavePressureCoeff (D : Vec3 →L[ℝ] Vec3) (k a : Vec3) : ℝ :=
  2 * ⟪k, D a⟫_ℝ / ‖k‖ ^ 2

/-- The pressure at a fixed time in Lemma 2.1, with `S = D' + D²`. -/
noncomputable def affineWavePressure (P : ℝ → ℝ) (S : Vec3 →L[ℝ] Vec3)
    (p : ℝ) (k : Vec3) (x : Vec3) : ℝ :=
  -(1 / 2 : ℝ) * ⟪x, S x⟫_ℝ - p * P ⟪k, x⟫_ℝ

/-- The standard oriented cross product on three-dimensional Euclidean space. -/
noncomputable def cross3 (k a : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (crossProduct k.ofLp a.ofLp)

end TorusEuler

namespace TorusEuler.MovingWaveVector

abbrev Space := EuclideanSpace ℝ (Fin 3)

def frame (kp ap : ℝ → Space) (t : ℝ) : Fin 3 → Space :=
  ![NormedSpace.normalize (kp t), NormedSpace.normalize (ap t),
    cross3 (NormedSpace.normalize (kp t)) (NormedSpace.normalize (ap t))]

def entry (e : Fin 3 → Space) (A : Space →L[ℝ] Space) (i j : Fin 3) : ℝ :=
  ⟪e i, A (e j)⟫_ℝ

end TorusEuler.MovingWaveVector

namespace TorusEuler.PaperAffine

/-- The two equations of (2.1) on a prescribed interval. -/
def WaveOn (J : Set ℝ) (D : ℝ → Vec3 →L[ℝ] Vec3) (k a : ℝ → Vec3) : Prop :=
  (∀ t ∈ J, HasDerivWithinAt k (-((D t).adjoint (k t))) J t) ∧
  (∀ t ∈ J, HasDerivWithinAt a (affineWaveAmplitudeOperator (D t) (k t) (a t)) J t)

end TorusEuler.PaperAffine

end


