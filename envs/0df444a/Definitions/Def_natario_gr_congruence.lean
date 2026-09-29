-- Prove2me | Definitions.Def_natario_gr_congruence
-- name    : natario_gr_congruence
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T13:57:11.22406+00:00
-- url     : https://prove2.me/theorems/0ca6e900-cac0-4f1e-bac3-7212e172fb6b
-- title:
--   Covariant derivatives of fields, and unit timelike geodesic congruences
-- statement:
--   Covariant derivatives of vector fields, one-forms and covariant 2-tensors in the coordinate framework, and the kinematics of a congruence of unit timelike geodesics: its second fundamental form, spatial metric, expansion, shear and vorticity.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, Chapter 4 (Singularity theorems), §4.1

import Definitions.Def_natario_gr_curves

open scoped ContDiff

/-!
# Covariant derivatives of fields, and timelike geodesic congruences

Continuation of the coordinate framework for J. Natário, *Mathematical Relativity*
(arXiv:2003.02855), Chapter 4, §4.1.
-/

namespace MathematicalRelativity

namespace Spacetime

variable (m : Spacetime)

/-- `∇_b V^a`, the covariant derivative of a vector field. -/
noncomputable def covVec (V : Pt → Pt) (a b : Fin 4) (x : Pt) : ℝ :=
  pd (fun y => V y a) b x + ∑ c, m.christoffel a b c x * V x c

/-- `∇_u V_v`, the covariant derivative of the one-form metrically dual to `V`. -/
noncomputable def covCov (V : Pt → Pt) (u v : Fin 4) (x : Pt) : ℝ :=
  pd (fun y => m.lower y (V y) v) u x - ∑ a, m.christoffel a u v x * m.lower x (V x) a

/-- `∇_a T_{uv}`, the covariant derivative of a covariant 2-tensor field. -/
noncomputable def covT2 (T : Fin 4 → Fin 4 → Pt → ℝ) (a u v : Fin 4) (x : Pt) : ℝ :=
  pd (T u v) a x - ∑ b, m.christoffel b a u x * T b v x
    - ∑ b, m.christoffel b a v x * T u b x

/-- The divergence `∇_a V^a` of a vector field. -/
noncomputable def divergence (V : Pt → Pt) (x : Pt) : ℝ := ∑ a, m.covVec V a a x

end Spacetime

/-- A unit timelike geodesic congruence: a smooth, future-pointing, unit timelike vector
field whose integral curves are geodesics (Natário, §4.1). -/
structure Congruence (m : Spacetime) where
  X : Pt → Pt
  smooth : ∀ a, ContDiff ℝ ∞ (fun x => X x a)
  unit : ∀ x, m.ip x (X x) (X x) = -1
  future : ∀ x, Spacetime.IsFuture (X x)
  geodesic : ∀ x a, ∑ b, m.covVec X a b x * X x b = 0

namespace Congruence

variable {m : Spacetime}

/-- The second fundamental form `B_{μν} = ∇_ν X_μ` of the congruence (Natário, §4.1). -/
noncomputable def B (K : Congruence m) (u v : Fin 4) (x : Pt) : ℝ := m.covCov K.X v u x

/-- The spatial metric `h_{μν} = g_{μν} + X_μ X_ν` (Natário, Def. 4.1.4). -/
noncomputable def h (K : Congruence m) (u v : Fin 4) (x : Pt) : ℝ :=
  m.g x u v + m.lower x (K.X x) u * m.lower x (K.X x) v

/-- The expansion `θ = g^{μν} B_{μν}` (Natário, Def. 4.1.4). -/
noncomputable def expansion (K : Congruence m) (x : Pt) : ℝ :=
  ∑ u, ∑ v, m.ginv x u v * K.B u v x

/-- The shear `σ_{μν} = B_{(μν)} - (θ/3) h_{μν}` (Natário, Def. 4.1.4). -/
noncomputable def shear (K : Congruence m) (u v : Fin 4) (x : Pt) : ℝ :=
  (1/2 : ℝ) * (K.B u v x + K.B v u x) - (K.expansion x / 3) * K.h u v x

/-- The vorticity `ω_{μν} = B_{[μν]}` (Natário, Def. 4.1.4). -/
noncomputable def vorticity (K : Congruence m) (u v : Fin 4) (x : Pt) : ℝ :=
  (1/2 : ℝ) * (K.B u v x - K.B v u x)

/-- The contraction `σ_{μν} σ^{μν}`. -/
noncomputable def shearSq (K : Congruence m) (x : Pt) : ℝ :=
  ∑ u, ∑ v, ∑ p, ∑ q, m.ginv x u p * m.ginv x v q * K.shear u v x * K.shear p q x

/-- The contraction `ω_{μν} ω^{μν}`. -/
noncomputable def vorticitySq (K : Congruence m) (x : Pt) : ℝ :=
  ∑ u, ∑ v, ∑ p, ∑ q, m.ginv x u p * m.ginv x v q * K.vorticity u v x * K.vorticity p q x

/-- The derivative `X · f` of a scalar field along the congruence. -/
noncomputable def along (K : Congruence m) (f : Pt → ℝ) (x : Pt) : ℝ :=
  ∑ a, K.X x a * pd f a x

/-- `c` is an integral curve of the congruence on `I`. -/
def IsIntegralCurveOn (K : Congruence m) (c : ℝ → Pt) (I : Set ℝ) : Prop :=
  (∀ a, ContDiffOn ℝ 2 (fun s => c s a) I) ∧ ∀ t ∈ I, vel c t = K.X (c t)

end Congruence

end MathematicalRelativity


